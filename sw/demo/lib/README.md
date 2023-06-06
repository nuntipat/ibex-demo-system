This directory contain libraries which are shared by several test program.

# Setup Instruction

## TensorFlow Lite Micro

1. Generate the required source/header files using the script in the the TensorFlow Lite Micro repository

    ```shell
    git clone https://github.com/tensorflow/tflite-micro.git
    cd tflite-micro
    python tensorflow/lite/micro/tools/project_generation/create_tflm_tree.py ../tfmicro_riscv_lib --makefile_options="TARGET=riscv32imac_ilp32d_generic"
    cd ../
    rm -rf tflite-micro
    ```