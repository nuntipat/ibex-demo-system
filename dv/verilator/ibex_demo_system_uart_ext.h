#include "sim_ctrl_extension.h"
#include <vector>
#include <map>
#include <verilated.h>
#include <fstream>

struct UartData {
    int time;
    std::vector<int> data;
};

class IbexUartUtil : public SimCtrlExtension {
public:
    IbexUartUtil(CData* tx, CData* rx, int baudrate, int numDataBits, int numStopBits, int sysclk);
    bool ParseCLIArguments(int argc, char **argv, bool &exit_app) override;
    void PreExec() override;
    void OnClock(unsigned long sim_time) override;
    void PostExec() override;

private:
    bool loadInitFile(std::string filePath);

    CData* _tx;
    CData* _rx;
    const int _baudrate;
    const int _numDataBits;
    const int _numStopBits;
    const int _sysclk;
    const int _bitNumCycles;

    bool _hasFrameStart;
    int _numBitReceived;
    int _recievedBuffer;
    unsigned long _nextSamplingCycle;

    int _currentTestIndex;
    int _currentTestDataByteIndex;
    int _currentTestDataBitIndex;
    std::vector<UartData> _transmitBuffer;
    unsigned long _nextTxSamplingCycle;

    std::string _uartInitFile;
    std::string _uartLogFilePath;
    std::ofstream _uartLogFile;
};