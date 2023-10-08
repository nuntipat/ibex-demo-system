#include "verilated_toplevel.h"
#include "sim_ctrl_extension.h"
#include <deque>
#include <verilated.h>
#include <fstream>

struct TraceData {
    unsigned long cycle;
    unsigned int fetchId;
    unsigned int pc;
    unsigned int inst;
    unsigned int rd;
    unsigned int rdValue;
    unsigned int rdWriteEnable;
    unsigned int rs1;
    unsigned int rs1Value;
    unsigned int rs2;
    unsigned int rs2Value;
}; 

class IbexTraceUtil : public SimCtrlExtension {
public:
    IbexTraceUtil(ibex_demo_system* top_module);
    bool ParseCLIArguments(int argc, char **argv, bool &exit_app) override;
    void OnClock(unsigned long sim_time) override;
    void PostExec() override;

private:
    CData* _ready_i;
    CData* _valid_o;
    IData* _rdata_o;
    IData* _addr_o;
    IData* _fetch_id_idex;
    CData* raddr_a_i;
    IData* rdata_a_o;
    CData* raddr_b_i;
    IData* rdata_b_o;
    CData* waddr_a_i;
    IData* wdata_a_i;
    CData* we_a_i;

    std::deque<TraceData> _inst;
    std::ofstream _traceFile;
};