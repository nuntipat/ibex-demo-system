#include "ibex_demo_system_trace_ext.h"
#include "Vibex_demo_system__Syms.h"
#include <iostream>
#include <fstream>
#include <vector>
#include <getopt.h>

#define CLI_INST_TRACE_FILE 2000 

IbexTraceUtil::IbexTraceUtil(ibex_demo_system* top_module) 
    : _ready_i(&top_module->rootp->ibex_demo_system__DOT__u_top__DOT__u_ibex_core__DOT__if_stage_i__DOT__gen_prefetch_buffer__DOT__prefetch_buffer_i__DOT__ready_i)
    , _valid_o(&top_module->rootp->ibex_demo_system__DOT__u_top__DOT__u_ibex_core__DOT__if_stage_i__DOT__gen_prefetch_buffer__DOT__prefetch_buffer_i__DOT__valid_o)
    , _rdata_o(&top_module->rootp->ibex_demo_system__DOT__u_top__DOT__u_ibex_core__DOT__if_stage_i__DOT__gen_prefetch_buffer__DOT__prefetch_buffer_i__DOT__rdata_o)
    , _addr_o(&top_module->rootp->ibex_demo_system__DOT__u_top__DOT__u_ibex_core__DOT__if_stage_i__DOT__gen_prefetch_buffer__DOT__prefetch_buffer_i__DOT__addr_o)
    , _fetch_id_idex(&top_module->rootp->ibex_demo_system__DOT__u_top__DOT__u_ibex_core__DOT__if_stage_i__DOT__gen_prefetch_buffer__DOT__prefetch_buffer_i__DOT__fetch_id_idex)
    , raddr_a_i(&top_module->rootp->ibex_demo_system__DOT__u_top__DOT__gen_regfile_fpga__DOT__register_file_i__DOT__raddr_a_i)
    , rdata_a_o(&top_module->rootp->ibex_demo_system__DOT__u_top__DOT__gen_regfile_fpga__DOT__register_file_i__DOT__rdata_a_o)
    , raddr_b_i(&top_module->rootp->ibex_demo_system__DOT__u_top__DOT__gen_regfile_fpga__DOT__register_file_i__DOT__raddr_b_i)
    , rdata_b_o(&top_module->rootp->ibex_demo_system__DOT__u_top__DOT__gen_regfile_fpga__DOT__register_file_i__DOT__rdata_b_o)
    , waddr_a_i(&top_module->rootp->ibex_demo_system__DOT__u_top__DOT__gen_regfile_fpga__DOT__register_file_i__DOT__waddr_a_i)
    , wdata_a_i(&top_module->rootp->ibex_demo_system__DOT__u_top__DOT__gen_regfile_fpga__DOT__register_file_i__DOT__wdata_a_i)
    , we_a_i(&top_module->rootp->ibex_demo_system__DOT__u_top__DOT__gen_regfile_fpga__DOT__register_file_i__DOT__we_a_i) {
}

static void PrintHelp() {
    std::cout << "Trace utilities:\n\n"
                 "--inst-trace-file=FILE\n"
                 "  Log the instruction sequence and register value to file\n\n"
                 "-h|--help\n"
                 "  Show help\n\n";
}

bool IbexTraceUtil::ParseCLIArguments(int argc, char **argv, bool &exit_app) {
    const struct option long_options[] = {
      {"inst-trace-file", required_argument, nullptr, CLI_INST_TRACE_FILE},
      {"help", no_argument, nullptr, 'h'},
      {nullptr, no_argument, nullptr, 0}};

    std::string instTraceFilePath;

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
            case CLI_INST_TRACE_FILE:
                instTraceFilePath = optarg;
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

    if (!instTraceFilePath.empty()) {
        _traceFile.open(instTraceFilePath);
        if (!_traceFile.is_open()) {
            std::cerr << "ERROR: can't create the instruction trace file at " << instTraceFilePath << std::endl;
            return false;
        }
    }
    
    return true;
}

void IbexTraceUtil::OnClock(unsigned long sim_time) {
    unsigned long cycle = sim_time / 2;

    if (!_inst.empty() && *_ready_i) {
        _traceFile << std::dec << _inst[0].fetchId << " " 
                    << std::hex << _inst[0].pc << " " 
                    << std::hex << _inst[0].inst << " " 
                    << std::dec << static_cast<int>(*raddr_a_i) << " " 
                    << std::hex << *rdata_a_o << " " 
                    << std::dec << static_cast<int>(*raddr_b_i) << " " 
                    << std::hex << *rdata_b_o << " " 
                    << std::dec << static_cast<int>(*waddr_a_i) << " " 
                    << std::hex << *wdata_a_i << " " 
                    << std::dec << static_cast<int>(*we_a_i) << " " 
                    << std::endl;
        _inst.pop_front();
    }

    if (*_ready_i && *_valid_o) { 
        _inst.push_back({
            .cycle=cycle,
            .fetchId=*_fetch_id_idex,
            .pc=*_addr_o,
            .inst=*_rdata_o,
        });
    }
}

void IbexTraceUtil::PostExec() {
    if (_traceFile.is_open()) {
        _traceFile.close();
    }
}
