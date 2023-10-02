#include "ibex_demo_system_uart_ext.h"
#include <iostream>
#include <cstdlib>
#include <fstream>
#include <sstream>
#include <vector>
#include <getopt.h>

#define CLI_UART_INIT_FROM_FILE 1000
#define CLI_LOG_UART_TX_OPT 1001

IbexUartUtil::IbexUartUtil(CData *tx, CData *rx, int baudrate, int numDataBits, int numStopBits, int sysclk)
    : _tx(tx)
    , _rx(rx)
    , _baudrate(baudrate)
    , _numDataBits(numDataBits)
    , _numStopBits(numStopBits)
    , _sysclk(sysclk)
    , _bitNumCycles(sysclk / baudrate)
    , _hasFrameStart(false)
    , _currentTestIndex(0)
    , _currentTestDataByteIndex(0)
    , _currentTestDataBitIndex(0)
    , _nextTxSamplingCycle(0) {
}

static void PrintHelp() {
    std::cout << "Simulation uart utilities:\n\n"
                 "--uartinit=FILE\n"
                 "  Load a test pattern from a text file containing time in second\n"
                 "  follow by data to be sent in hexadecimal separate by a space\n"
                 "      0.001 0A 0B 0C 0D\n"
                 "      0.02  10 20\n"
                 "      ...\n\n"
                 "--log-uart-tx-to-file=FILE\n"
                 "  Log the data output from the uart tx pin to file\n\n"
                 "-h|--help\n"
                 "  Show help\n\n";
}

bool IbexUartUtil::loadInitFile(std::string filePath) {
    std::ifstream initfile(filePath);
    if (!initfile.is_open()) {
        std::cerr << "ERROR: can't open the uart initialize file at " << filePath << std::endl;
        return false;
    }

    std::string line;
    int lineNumber = 0;
    while (getline(initfile, line)) {
        if (!line.empty() && line[line.size() - 1] == '\r') {
            line.erase(line.size() - 1);
        }
        std::istringstream iss(line);
        
        double time;
        iss >> time;
        if (!iss.good()) {
            std::cerr << "ERROR: format error in the uart initialize file at line " << lineNumber << std::endl;
            return false;
        }
        int cycle = time * _sysclk;
        // std::cout << time << std::endl;

        std::vector<int> data;
        int tmp;
        while (iss.good()) {
            iss >> std::hex >> tmp;
            if (iss.fail()) {
                std::cerr << "ERROR: format error in the uart initialize file at line " << lineNumber << std::endl;
                return false;
            }
            data.push_back(tmp);
        }
        
        _transmitBuffer.push_back({cycle, data});
        lineNumber++;
    }

    initfile.close();

    // for (const auto& frame : _transmitBuffer) {
    //     std::cout << "Time = " << frame.time << " Data = ";
    //     for (int n : frame.data) {
    //         std::cout << n << " ";
    //     }
    //     std::cout << std::endl;
    // }

    return true;
}

bool IbexUartUtil::ParseCLIArguments(int argc, char **argv, bool &exit_app) {
    const struct option long_options[] = {
      {"uartinit", required_argument, nullptr, CLI_UART_INIT_FROM_FILE},
      {"log-uart-tx-to-file", required_argument, nullptr, CLI_LOG_UART_TX_OPT},
      {"help", no_argument, nullptr, 'h'},
      {nullptr, no_argument, nullptr, 0}};

    // Reset the command parsing index in-case other utils have already parsed
    // some arguments
    optind = 1;
    while (1) {
        int c = getopt_long(argc, argv, "h", long_options, nullptr);
        if (c == -1) {
            break;
        }

        // Disable error reporting by getopt
        opterr = 0;

        switch (c) {
            case 0:
            case 1:
                break;
            case CLI_UART_INIT_FROM_FILE:
                _uartInitFile = optarg;
                break;
            case CLI_LOG_UART_TX_OPT:
                _uartLogFilePath = optarg;
                break;
            case 'h':
                PrintHelp();
                return true;
            case ':':  // missing argument
                std::cerr << "ERROR: Missing argument." << std::endl << std::endl;
                return false;
            case '?':
            default:;
            // Ignore unrecognized options since they might be consumed by
            // other utils
        }
    }

    if (!_uartInitFile.empty() && !loadInitFile(_uartInitFile)) {
        return false;
    }

    if (!_uartLogFilePath.empty()) {
        _uartLogFile.open(_uartLogFilePath);
        if (!_uartLogFile.is_open()) {
            std::cerr << "ERROR: can't create the uart log file at " << _uartLogFilePath << std::endl;
            return false;
        }
    }
    
    return true;
}

void IbexUartUtil::PreExec() {
    *_rx = 1;
}

void IbexUartUtil::OnClock(unsigned long sim_time) {
    unsigned long cycle = sim_time / 2;

    if (!_hasFrameStart) {
        // if the start bit is detected, reset all state variables for receiving next frame
        if (*_tx == 0) {
            _hasFrameStart = true;
            _numBitReceived = 0;
            _recievedBuffer = 0;
            _nextSamplingCycle = cycle + _bitNumCycles * 1.5; // skip the start bit and sampling at the middle of the first data bit
        }
    } else {
        // wait until we are in the middle of the next bit
        if (cycle >= _nextSamplingCycle) {
            if (_numBitReceived == _numDataBits) {  // stop bit
                // std::cout << "Received data as dec = " << _recievedBuffer << " as char = " << static_cast<char>(_recievedBuffer) << std::endl;
                if (_uartLogFile.is_open()) {
                    _uartLogFile << std::hex << _recievedBuffer << " ";
                }
                _hasFrameStart = false;
            } else {    // recieve the new bit
                _recievedBuffer = _recievedBuffer | (*_tx << _numBitReceived);
                _numBitReceived++;
                _nextSamplingCycle += _bitNumCycles;
            }
        }
    }

    if (_currentTestIndex < _transmitBuffer.size() && cycle >= _transmitBuffer[_currentTestIndex].time) {
        auto data = _transmitBuffer[_currentTestIndex].data;
        if (_currentTestDataByteIndex == data.size()) {
            _currentTestIndex++;
            _currentTestDataByteIndex = 0;
            _currentTestDataBitIndex = 0;
        } else {
            auto byte = data[_currentTestDataByteIndex];
            if (cycle >= _nextTxSamplingCycle) {
                if (_currentTestDataBitIndex == 0) {
                    *_rx = 0;
                    _currentTestDataBitIndex++;
                    _nextTxSamplingCycle = cycle + _bitNumCycles;
                } else if (_currentTestDataBitIndex <= _numDataBits) {
                    *_rx = (byte & (1 << (_currentTestDataBitIndex - 1))) >> (_currentTestDataBitIndex - 1);
                    _currentTestDataBitIndex++;
                    _nextTxSamplingCycle += _bitNumCycles;
                } else {
                    *_rx = 1;
                    _currentTestDataBitIndex = 0;
                    _currentTestDataByteIndex++;
                    _nextTxSamplingCycle += _bitNumCycles;
                }
            }
        }
    }
}

void IbexUartUtil::PostExec() {
    if (_uartLogFile.is_open()) {
        _uartLogFile.close();
    }
}