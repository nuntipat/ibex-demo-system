// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "verilated_toplevel.h"
#include "verilator_memutil.h"
#include "ibex_demo_system_uart_ext.h"

class DemoSystem {
 public:
  DemoSystem(const char *ram_hier_path, int ram_size_words);
  virtual ~DemoSystem() {}
  virtual int Main(int argc, char **argv);


 protected:
  ibex_demo_system _top;
  VerilatorMemUtil _memutil;
  MemArea _ram;
  IbexUartUtil _uartutil;

  virtual int Setup(int argc, char **argv, bool &exit_app);
  virtual void Run();
  virtual bool Finish();
};
