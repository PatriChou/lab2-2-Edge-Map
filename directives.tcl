//  Catapult Ultra Synthesis 2024.1/1091966 (Production Release) Wed Feb 14 09:07:18 PST 2024
//  
//          Copyright (c) Siemens EDA, 1996-2024, All Rights Reserved.
//                        UNPUBLISHED, LICENSED SOFTWARE.
//             CONFIDENTIAL AND PROPRIETARY INFORMATION WHICH IS THE
//                   PROPERTY OF SIEMENS EDA OR ITS LICENSORS.
//  
//  Running on Linux m111061605@ws34:17017 3.10.0-1160.95.1.el7.x86_64 x86_64 aol
//  
//  Package information: SIFLIBS v27.1_0.0, HLS_PKGS v27.1_0.0, 
//                       SIF_TOOLKITS v27.1_0.0, SIF_XILINX v27.1_0.0, 
//                       SIF_ALTERA v27.1_0.0, CCS_LIBS v27.1_0.0, 
//                       CDS_PPRO v2023.2_3, CDS_DesignChecker v2024.1, 
//                       CDS_OASYS v21.1_3.1, CDS_PSR v23.2_0.16, 
//                       DesignPad v2.78_1.0, DesignAnalyzer 2024.1/1090934
//  
solution new -state initial
solution options defaults
solution options set /OnTheFly/VthAttributeType cell_lib
solution options set /Input/SearchPath {/home/m111/m111061605/advanced_soc/catapult/catapult-for-soc-course/lab2_edgedetec_fsic/02_edgedetect_fsic/hls_c/inc /home/m111/m111061605/advanced_soc/catapult/catapult-for-soc-course/lab2_edgedetec_fsic/02_edgedetect_fsic/cmodel/inc /home/m111/m111061605/advanced_soc/catapult/catapult-for-soc-course/lab2_edgedetec_fsic/02_edgedetect_fsic/bmpUtil/inc}
solution options set /Output/GenerateCycleNetlist false
solution options set /Flows/SCVerify/INVOKE_ARGS {./bin/image/people640x360_rgb.bmp 1 out_algorithm.bmp out_hw.bmp}
solution file add ./hls_c/inc/EdgeDetect.h -type CHEADER
solution file add ./hls_c/src/EdgeDetect_tb.cpp -type C++ -exclude true
solution file add ./bmpUtil/src/bmp_io.cpp -type C++ -exclude true
directive set -DESIGN_GOAL area
directive set -SPECULATE true
directive set -MERGEABLE true
directive set -REGISTER_THRESHOLD 256
directive set -MEM_MAP_THRESHOLD 32
directive set -LOGIC_OPT false
directive set -FSM_ENCODING none
directive set -FSM_BINARY_ENCODING_THRESHOLD 64
directive set -REG_MAX_FANOUT 0
directive set -NO_X_ASSIGNMENTS true
directive set -SAFE_FSM false
directive set -REGISTER_SHARING_MAX_WIDTH_DIFFERENCE 8
directive set -REGISTER_SHARING_LIMIT 0
directive set -ASSIGN_OVERHEAD 0
directive set -TIMING_CHECKS true
directive set -MUXPATH true
directive set -REALLOC true
directive set -UNROLL no
directive set -IO_MODE super
directive set -CHAN_IO_PROTOCOL use_library
directive set -ARRAY_SIZE 1024
directive set -IDLE_SIGNAL {}
directive set -STALL_FLAG_SV off
directive set -STALL_FLAG false
directive set -TRANSACTION_DONE_SIGNAL true
directive set -DONE_FLAG {}
directive set -READY_FLAG {}
directive set -START_FLAG {}
directive set -TRANSACTION_SYNC ready
directive set -RESET_CLEARS_ALL_REGS use_library
directive set -CLOCK_OVERHEAD 20.000000
directive set -ON_THE_FLY_PROTOTYPING false
directive set -OPT_CONST_MULTS use_library
directive set -CHARACTERIZE_ROM false
directive set -PROTOTYPE_ROM true
directive set -ROM_THRESHOLD 64
directive set -CLUSTER_ADDTREE_IN_WIDTH_THRESHOLD 0
directive set -CLUSTER_ADDTREE_IN_COUNT_THRESHOLD 0
directive set -CLUSTER_OPT_CONSTANT_INPUTS true
directive set -CLUSTER_RTL_SYN false
directive set -CLUSTER_FAST_MODE false
directive set -CLUSTER_TYPE combinational
directive set -PIPELINE_RAMP_UP true
go new
go analyze
go compile
solution library add mgc_Xilinx-ZYNQ-1_beh -- -rtlsyntool Vivado -manufacturer Xilinx -family ZYNQ -speed -1 -part xc7z010clg400-1
solution library add Xilinx_RAMS
solution library add Xilinx_FIFO
go libraries
directive set -CLOCKS {clk {-CLOCK_PERIOD 10.0 -CLOCK_EDGE rising -CLOCK_UNCERTAINTY 0.0 -CLOCK_HIGH_TIME 5.0 -RESET_SYNC_NAME rst -RESET_ASYNC_NAME arst_n -RESET_KIND both -RESET_SYNC_ACTIVE high -RESET_ASYNC_ACTIVE low -ENABLE_ACTIVE high}}
go assembly
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_MagAng/widthIn:rsc -MAP_TO_MODULE {[DirectInput]}
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_MagAng/heightIn:rsc -MAP_TO_MODULE {[DirectInput]}
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_HorDer/widthIn:rsc -MAP_TO_MODULE {[DirectInput]}
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_HorDer/heightIn:rsc -MAP_TO_MODULE {[DirectInput]}
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_VerDer/widthIn:rsc -MAP_TO_MODULE {[DirectInput]}
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_VerDer/heightIn:rsc -MAP_TO_MODULE {[DirectInput]}
directive set /EdgeDetect_IP::EdgeDetect_Top/widthIn:rsc -MAP_TO_MODULE {[DirectInput]}
directive set /EdgeDetect_IP::EdgeDetect_Top/heightIn:rsc -MAP_TO_MODULE {[DirectInput]}
directive set /EdgeDetect_IP::EdgeDetect_Top/dx_chan:cns -FIFO_DEPTH 0
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_VerDer/run/line_buf0:rsc -EXTERNAL_MEMORY true
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_VerDer/run/line_buf0:rsc -GEN_EXTERNAL_ENABLE true
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_VerDer/run/line_buf1:rsc -EXTERNAL_MEMORY true
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_VerDer/run/line_buf1:rsc -GEN_EXTERNAL_ENABLE true
directive set /EdgeDetect_IP::EdgeDetect_Top/dy_chan:cns -FIFO_DEPTH 3
directive set /EdgeDetect_IP::EdgeDetect_Top/pix_chan1:cns -FIFO_DEPTH 1
directive set /EdgeDetect_IP::EdgeDetect_Top/pix_chan2:cns -FIFO_DEPTH 1
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_VerDer/dat_in:rsc -MAP_TO_MODULE ccs_ioport.ccs_in_wait_coupled
directive set /EdgeDetect_IP::EdgeDetect_Top/dat_in:rsc -MAP_TO_MODULE ccs_ioport.ccs_in_wait_coupled
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_VerDer/run/VCOL -PIPELINE_INIT_INTERVAL 1
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_VerDer/run/VCOL -PIPELINE_STALL_MODE flush
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_HorDer/run/HCOL -PIPELINE_STALL_MODE flush
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_MagAng/run/MCOL -PIPELINE_STALL_MODE flush
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_MagAng/run/MROW -PIPELINE_STALL_MODE flush
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_MagAng/run/main -PIPELINE_STALL_MODE flush
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_HorDer/run/HROW -PIPELINE_STALL_MODE flush
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_HorDer/run/main -PIPELINE_STALL_MODE flush
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_VerDer/run/main -PIPELINE_STALL_MODE flush
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_MagAng/run/main -PIPELINE_INIT_INTERVAL 0
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_MagAng/run/MROW -PIPELINE_INIT_INTERVAL 0
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_MagAng/run/MCOL -PIPELINE_INIT_INTERVAL 0
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_HorDer/run/main -PIPELINE_INIT_INTERVAL 0
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_HorDer/run/HROW -PIPELINE_INIT_INTERVAL 0
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_HorDer/run/HCOL -PIPELINE_INIT_INTERVAL 0
directive set /EdgeDetect_IP::EdgeDetect_Top/EdgeDetect_IP::EdgeDetect_VerDer/run/main -PIPELINE_INIT_INTERVAL 0
go architect
go extract
