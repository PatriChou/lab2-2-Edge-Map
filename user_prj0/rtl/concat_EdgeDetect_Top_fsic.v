
//------> /usr/cadtool/mentor/Catapult/2024.1/Mgc_home/pkgs/siflibs/ccs_in_wait_v1.v 
//------------------------------------------------------------------------------
// Catapult Synthesis - Sample I/O Port Library
//
// Copyright (c) 2003-2017 Mentor Graphics Corp.
//       All Rights Reserved
//
// This document may be used and distributed without restriction provided that
// this copyright statement is not removed from the file and that any derivative
// work contains this copyright notice.
//
// The design information contained in this file is intended to be an example
// of the functionality which the end user may study in preparation for creating
// their own custom interfaces. This design does not necessarily present a 
// complete implementation of the named protocol or standard.
//
//------------------------------------------------------------------------------


module ccs_in_wait_v1 (idat, rdy, ivld, dat, irdy, vld);

  parameter integer rscid = 1;
  parameter integer width = 8;

  output [width-1:0] idat;
  output             rdy;
  output             ivld;
  input  [width-1:0] dat;
  input              irdy;
  input              vld;

  wire   [width-1:0] idat;
  wire               rdy;
  wire               ivld;

  localparam stallOff = 0; 
  wire                  stall_ctrl;
  assign stall_ctrl = stallOff;

  assign idat = dat;
  assign rdy = irdy && !stall_ctrl;
  assign ivld = vld && !stall_ctrl;

endmodule


//------> /usr/cadtool/mentor/Catapult/2024.1/Mgc_home/pkgs/siflibs/mgc_inout_prereg_en_v1.v 
//------------------------------------------------------------------------------
// Catapult Synthesis - Sample I/O Port Library
//
// Copyright (c) 2003-2019 Mentor Graphics Corp.
//       All Rights Reserved
//
// This document may be used and distributed without restriction provided that
// this copyright statement is not removed from the file and that any derivative
// work contains this copyright notice.
//
// The design information contained in this file is intended to be an example
// of the functionality which the end user may study in preparation for creating
// their own custom interfaces. This design does not necessarily present a 
// complete implementation of the named protocol or standard.
//
//------------------------------------------------------------------------------


module mgc_inout_prereg_en_v1 (din, ldout, dout, zin, lzout, zout);

    parameter integer rscid = 1;
    parameter integer width = 8;

    output [width-1:0] din;
    input              ldout;
    input  [width-1:0] dout;
    input  [width-1:0] zin;
    output             lzout;
    output [width-1:0] zout;

    wire   [width-1:0] din;
    wire               lzin;
    wire               lzout;
    wire   [width-1:0] z;

    assign lzout = ldout;
    assign din = zin;
    assign zout = dout;

endmodule



//------> /usr/cadtool/mentor/Catapult/2024.1/Mgc_home/pkgs/siflibs/ccs_out_wait_v1.v 
//------------------------------------------------------------------------------
// Catapult Synthesis - Sample I/O Port Library
//
// Copyright (c) 2003-2017 Mentor Graphics Corp.
//       All Rights Reserved
//
// This document may be used and distributed without restriction provided that
// this copyright statement is not removed from the file and that any derivative
// work contains this copyright notice.
//
// The design information contained in this file is intended to be an example
// of the functionality which the end user may study in preparation for creating
// their own custom interfaces. This design does not necessarily present a 
// complete implementation of the named protocol or standard.
//
//------------------------------------------------------------------------------


module ccs_out_wait_v1 (dat, irdy, vld, idat, rdy, ivld);

  parameter integer rscid = 1;
  parameter integer width = 8;

  output [width-1:0] dat;
  output             irdy;
  output             vld;
  input  [width-1:0] idat;
  input              rdy;
  input              ivld;

  wire   [width-1:0] dat;
  wire               irdy;
  wire               vld;

  localparam stallOff = 0; 
  wire stall_ctrl;
  assign stall_ctrl = stallOff;

  assign dat = idat;
  assign irdy = rdy && !stall_ctrl;
  assign vld = ivld && !stall_ctrl;

endmodule



//------> /usr/cadtool/mentor/Catapult/2024.1/Mgc_home/pkgs/siflibs/mgc_io_sync_v2.v 
//------------------------------------------------------------------------------
// Catapult Synthesis - Sample I/O Port Library
//
// Copyright (c) 2003-2017 Mentor Graphics Corp.
//       All Rights Reserved
//
// This document may be used and distributed without restriction provided that
// this copyright statement is not removed from the file and that any derivative
// work contains this copyright notice.
//
// The design information contained in this file is intended to be an example
// of the functionality which the end user may study in preparation for creating
// their own custom interfaces. This design does not necessarily present a 
// complete implementation of the named protocol or standard.
//
//------------------------------------------------------------------------------


module mgc_io_sync_v2 (ld, lz);
    parameter valid = 0;

    input  ld;
    output lz;

    wire   lz;

    assign lz = ld;

endmodule


//------> /usr/cadtool/mentor/Catapult/2024.1/Mgc_home/pkgs/siflibs/ccs_in_v1.v 
//------------------------------------------------------------------------------
// Catapult Synthesis - Sample I/O Port Library
//
// Copyright (c) 2003-2017 Mentor Graphics Corp.
//       All Rights Reserved
//
// This document may be used and distributed without restriction provided that
// this copyright statement is not removed from the file and that any derivative
// work contains this copyright notice.
//
// The design information contained in this file is intended to be an example
// of the functionality which the end user may study in preparation for creating
// their own custom interfaces. This design does not necessarily present a 
// complete implementation of the named protocol or standard.
//
//------------------------------------------------------------------------------


module ccs_in_v1 (idat, dat);

  parameter integer rscid = 1;
  parameter integer width = 8;

  output [width-1:0] idat;
  input  [width-1:0] dat;

  wire   [width-1:0] idat;

  assign idat = dat;

endmodule


//------> /usr/cadtool/mentor/Catapult/2024.1/Mgc_home/pkgs/siflibs/ccs_in_wait_coupled_v1.v 
//------------------------------------------------------------------------------
// Catapult Synthesis - Sample I/O Port Library
//
// Copyright (c) 2003-2017 Mentor Graphics Corp.
//       All Rights Reserved
//
// This document may be used and distributed without restriction provided that
// this copyright statement is not removed from the file and that any derivative
// work contains this copyright notice.
//
// The design information contained in this file is intended to be an example
// of the functionality which the end user may study in preparation for creating
// their own custom interfaces. This design does not necessarily present a 
// complete implementation of the named protocol or standard.
//
//------------------------------------------------------------------------------


module ccs_in_wait_coupled_v1 (idat, rdy, ivld, dat, irdy, vld);

  parameter integer rscid = 1;
  parameter integer width = 8;

  output [width-1:0] idat;
  output             rdy;
  output             ivld;
  input  [width-1:0] dat;
  input              irdy;
  input              vld;

  wire   [width-1:0] idat;
  wire               rdy;
  wire               ivld;

  assign idat = dat;
  assign rdy = irdy;
  assign ivld = vld;

endmodule


//------> /usr/cadtool/mentor/Catapult/2024.1/Mgc_home/pkgs/siflibs/ccs_genreg_v1.v 
//------------------------------------------------------------------------------
// Catapult Synthesis - Sample I/O Port Library
//
// Copyright (c) 2003-2017 Mentor Graphics Corp.
//       All Rights Reserved
//
// This document may be used and distributed without restriction provided that
// this copyright statement is not removed from the file and that any derivative
// work contains this copyright notice.
//
// The design information contained in this file is intended to be an example
// of the functionality which the end user may study in preparation for creating
// their own custom interfaces. This design does not necessarily present a 
// complete implementation of the named protocol or standard.
//
//------------------------------------------------------------------------------

module ccs_genreg_v1 (clk, en, arst, srst, d, z);
    parameter integer width   = 1;
    parameter integer ph_clk  = 1;
    parameter integer ph_en   = 1;
    parameter integer ph_arst = 0;
    parameter integer ph_srst = 1;
    parameter         has_en  = 1'b1;

    input clk;
    input en;
    input arst;
    input srst;
    input      [width-1:0] d;
    output reg [width-1:0] z;

    //  Generate parameters
    //  ph_clk | ph_arst | has_en     Label:
    //    1        1          1       GEN_CLK1_ARST1_EN1
    //    1        1          0       GEN_CLK1_ARST1_EN0
    //    1        0          1       GEN_CLK1_ARST0_EN1
    //    1        0          0       GEN_CLK1_ARST0_EN0
    //    0        1          1       GEN_CLK0_ARST1_EN1
    //    0        1          0       GEN_CLK0_ARST1_EN0
    //    0        0          1       GEN_CLK0_ARST0_EN1
    //    0        0          0       GEN_CLK0_ARST0_EN0
    
    generate 
      // Pos edge clock, pos edge async reset, has enable
      if (ph_clk == 1 & ph_arst == 1 & has_en == 1)
      begin: GEN_CLK1_ARST1_EN1
        always @(posedge clk or posedge arst)
          if (arst == 1'b1)
            z <= {width{1'b0}};
          else if (srst == $unsigned(ph_srst))
            z <= {width{1'b0}};
          else if (en == $unsigned(ph_en))
            z <= d;
      end  //GEN_CLK1_ARST1_EN1

      // Pos edge clock, pos edge async reset, no enable
      else if (ph_clk == 1 & ph_arst == 1 & has_en == 0)
      begin: GEN_CLK1_ARST1_EN0
        always @(posedge clk or posedge arst)
          if (arst == 1'b1)
            z <= {width{1'b0}};
          else if (srst == $unsigned(ph_srst))
            z <= {width{1'b0}};
          else
            z <= d;
      end  //GEN_CLK1_ARST1_EN0

      // Pos edge clock, neg edge async reset, has enable
      else if (ph_clk == 1 & ph_arst == 0 & has_en == 1)
      begin: GEN_CLK1_ARST0_EN1
        always @(posedge clk or negedge arst)
          if (arst == 1'b0)
            z <= {width{1'b0}};
          else if (srst == $unsigned(ph_srst))
            z <= {width{1'b0}};
          else if (en == $unsigned(ph_en))
            z <= d;
      end  //GEN_CLK1_ARST0_EN1

      // Pos edge clock, neg edge async reset, no enable
      else if (ph_clk == 1 & ph_arst == 0 & has_en == 0)
      begin: GEN_CLK1_ARST0_EN0
        always @(posedge clk or negedge arst)
          if (arst == 1'b0)
            z <= {width{1'b0}};
          else if (srst == $unsigned(ph_srst))
            z <= {width{1'b0}};
          else
            z <= d;
      end  //GEN_CLK1_ARST0_EN0


      // Neg edge clock, pos edge async reset, has enable
      if (ph_clk == 0 & ph_arst == 1 & has_en == 1)
      begin: GEN_CLK0_ARST1_EN1
        always @(negedge clk or posedge arst)
          if (arst == 1'b1)
            z <= {width{1'b0}};
          else if (srst == $unsigned(ph_srst))
            z <= {width{1'b0}};
          else if (en == $unsigned(ph_en))
            z <= d;
      end  //GEN_CLK0_ARST1_EN1

      // Neg edge clock, pos edge async reset, no enable
      else if (ph_clk == 0 & ph_arst == 1 & has_en == 0)
      begin: GEN_CLK0_ARST1_EN0
        always @(negedge clk or posedge arst)
          if (arst == 1'b1)
            z <= {width{1'b0}};
          else if (srst == $unsigned(ph_srst))
            z <= {width{1'b0}};
          else
            z <= d;
      end  //GEN_CLK0_ARST1_EN0

      // Neg edge clock, neg edge async reset, has enable
      else if (ph_clk == 0 & ph_arst == 0 & has_en == 1)
      begin: GEN_CLK0_ARST0_EN1
        always @(negedge clk or negedge arst)
          if (arst == 1'b0)
            z <= {width{1'b0}};
          else if (srst == $unsigned(ph_srst))
            z <= {width{1'b0}};
          else if (en == $unsigned(ph_en))
            z <= d;
      end  //GEN_CLK0_ARST0_EN1

      // Neg edge clock, neg edge async reset, no enable
      else if (ph_clk == 0 & ph_arst == 0 & has_en == 0)
      begin: GEN_CLK0_ARST0_EN0
        always @(negedge clk or negedge arst)
          if (arst == 1'b0)
            z <= {width{1'b0}};
          else if (srst == $unsigned(ph_srst))
            z <= {width{1'b0}};
          else
            z <= d;
      end  //GEN_CLK0_ARST0_EN0
    endgenerate
endmodule


//------> /usr/cadtool/mentor/Catapult/2024.1/Mgc_home/pkgs/siflibs/ccs_fifo_wait_core_v5.v 
//------------------------------------------------------------------------------
// Catapult Synthesis - Sample I/O Port Library
//
// Copyright (c) 2003-2017 Mentor Graphics Corp.
//       All Rights Reserved
//
// This document may be used and distributed without restriction provided that
// this copyright statement is not removed from the file and that any derivative
// work contains this copyright notice.
//
// The design information contained in this file is intended to be an example
// of the functionality which the end user may study in preparation for creating
// their own custom interfaces. This design does not necessarily present a 
// complete implementation of the named protocol or standard.
//
//------------------------------------------------------------------------------

/*
 *            _________________________________________________
 * WRITER    |                                                 |   READER
 *           |               ccs_fifo_wait_core                |
 *           |             _____________________               |
 *        --<|  din_rdy --<|  ---------------- <|--- dout_rdy <|---
 *           |             |       FIFO         |              |
 *        ---|> din_vld ---|> ----------------  |>-- dout_vld  |>--
 *        ---|>     din ---|> ----------------  |>-- dout      |>--
 *           |             |____________________|              |
 *           |_________________________________________________|
 *
 *    rdy    - can be considered as a notFULL signal
 *    vld    - can be considered as a notEMPTY signal
 *    is_idle - clk can be safely gated
 *
 * Change History:
 *    2019-01-24 - Add assertion to verify rdy signal behavior under reset.
 *                 Fix bug in that behavior.
 */

module ccs_fifo_wait_core_v5 (clk, en, arst, srst, din_vld, din_rdy, din, dout_vld, dout_rdy, dout, sd, is_idle);

    parameter integer rscid    = 0;     // resource ID
    parameter integer width    = 8;     // fifo width
    parameter integer sz_width = 8;     // size of port for elements in fifo
    parameter integer fifo_sz  = 8;     // fifo depth
    parameter integer ph_clk   = 1;     // clock polarity 1=rising edge, 0=falling edge
    parameter integer ph_en    = 1;     // clock enable polarity
    parameter integer ph_arst  = 1;     // async reset polarity
    parameter integer ph_srst  = 1;     // sync reset polarity
    parameter integer ph_log2  = 3;     // log2(fifo_sz)

    input                 clk;
    input                 en;
    input                 arst;
    input                 srst;
    input                 din_vld;    // writer has valid data
    output                din_rdy;    // fifo ready for data (not full)
    input  [width-1:0]    din;
    output                dout_vld;   // fifo has valid data (not empty)
    input                 dout_rdy;   // reader ready for data
    output [width-1:0]    dout;
    output [sz_width-1:0] sd;
    output                is_idle;

    localparam integer fifo_b  = width * fifo_sz;
    localparam integer fifo_mx = (fifo_sz > 0) ? (fifo_sz-1) : 0 ;
    localparam integer fifo_mx_over_8 = fifo_mx / 8 ;

    reg      [fifo_mx:0] stat_pre;
    wire     [fifo_mx:0] stat;
    reg      [( (fifo_b > 0) ? fifo_b : 1)-1:0] buff_pre;
    wire     [( (fifo_b > 0) ? fifo_b : 1)-1:0] buff;
    reg      [fifo_mx:0] en_l;
    reg      [fifo_mx_over_8:0] en_l_s;

    reg      [width-1:0] buff_nxt;

    reg                  stat_nxt;
    reg                  stat_behind;
    reg                  stat_ahead;
    reg                  stat_tail;
    reg                  en_l_var;

    integer              i;
    genvar               eni;

    wire [32:0]          size_t;
    reg  [31:0]          count;
    reg  [31:0]          count_t;
    reg  [32:0]          n_elem;
    wire                 din_rdy_drv;
    wire                 dout_vld_drv;
    wire                 din_vld_int;
    wire                 hs_init;
    wire                 active;
    wire                 is_idle_drv;

    // synopsys translate_off
    reg  [31:0]          peak;
    initial
    begin
      peak  = 32'b0;
    end
    // synopsys translate_on

    assign din_rdy = din_rdy_drv;
    assign dout_vld = dout_vld_drv;
    assign is_idle = is_idle_drv;

    generate
    if ( fifo_sz > 0 )
    begin: FIFO_REG
      assign din_vld_int = din_vld & hs_init;
      assign din_rdy_drv = (dout_rdy | (~stat[0])) & hs_init;
      assign dout_vld_drv = din_vld_int | stat[fifo_sz-1];

      assign active = (din_vld_int & din_rdy_drv) | (dout_rdy & dout_vld_drv);
      assign is_idle_drv = (~active) & hs_init;

      assign size_t = (count - {31'b0, (dout_rdy & stat[fifo_sz-1])}) + {31'b0, din_vld_int};
      assign sd = size_t[sz_width-1:0];

      assign dout = (stat[fifo_sz-1]) ? buff[fifo_b-1:width*(fifo_sz-1)] : din;

      always @(*)
      begin: FIFOPROC
        n_elem = 33'b0;
        for (i = fifo_sz-1; i >= 0; i = i - 1)
        begin
          stat_behind = (i != 0) ? stat[i-1] : 1'b0;
          stat_ahead  = (i != (fifo_sz-1)) ? stat[i+1] : 1'b1;

          // Determine if this buffer element will have data
          stat_nxt = stat_ahead &                       // valid element ahead of this one (or head)
                       (stat_behind                     // valid element behind this one
                         | (stat[i] & (~dout_rdy))      // valid element and output not ready (in use and not shifted)
                         | (stat[i] & din_vld_int)      // valid element and input has data
                         | (din_vld_int & (~dout_rdy))  // input has data and output not ready
                       );
          stat_pre[i] = stat_nxt;

          // First empty elem when not shifting or last valid elem after shifting (assumes stat_behind == 0)
          stat_tail = stat_ahead & (((~stat[i]) & (~dout_rdy)) | (stat[i] & dout_rdy));

          if (dout_rdy & stat_behind)
          begin
            // shift valid element
            buff_nxt[0+:width] = buff[width*(i-1)+:width];
            en_l_var = 1'b1;
          end
          else if (din_vld_int & stat_tail)
          begin
            // update tail with input data
            buff_nxt = din;
            en_l_var = 1'b1;
          end
          else
          begin
            // no-op, disable register
            buff_nxt = din; // Don't care input to disabled flop
            en_l_var = 1'b0;
          end
          buff_pre[width*i+:width] = buff_nxt[0+:width];

          if (ph_en != 0)
            en_l[i] = en & en_l_var;
          else
            en_l[i] = en | ~en_l_var;

          if ((stat_ahead == 1'b1) & (stat[i] == 1'b0))
            //found tail, update the number of elements for count
            n_elem = ($unsigned(fifo_sz) - 1) - $unsigned(i);
        end //for loop

        // Enable for stat registers (partitioned into banks of eight)
        // Take care of the head first
        if (ph_en != 0)
          en_l_s[(((fifo_sz > 0) ? fifo_sz : 1)-1)/8] = en & active;
        else
          en_l_s[(((fifo_sz > 0) ? fifo_sz : 1)-1)/8] = en | ~active;

        // Now every eight
        for (i = fifo_sz-1; i >= 7; i = i - 1)
        begin
          if (($unsigned(i) % 32'd8) == 0)
          begin
            if (ph_en != 0)
              en_l_s[(i/8)-1] = en & (stat[i]) & (active);
            else
              en_l_s[(i/8)-1] = (en) | (~stat[i]) | (~active);
          end
        end

        // Update count and peak
        if ( stat[fifo_sz-1] == 1'b0 )
          count_t = 32'b0;
        else if ( stat[0] == 1'b1 )
          count_t = fifo_sz;
        else
          count_t = n_elem[31:0];
        count = count_t;
        // synopsys translate_off
        peak = (peak < count) ? count : peak;
        // synopsys translate_on
      end //FIFOPROC

      // Handshake valid after reset
      ccs_genreg_v1
      #(
        .width   (1),
        .ph_clk  (ph_clk),
        .ph_en   (1),
        .ph_arst (ph_arst),
        .ph_srst (ph_srst),
        .has_en  (1'b0)
      )
      HS_INIT_REG
      (
        .clk     (clk),
        .en      (1'b1),
        .arst    (arst),
        .srst    (srst),
        .d       (1'b1),
        .z       (hs_init)
      );

      // Buffer and status registers
      for (eni = fifo_sz-1; eni >= 0; eni = eni - 1)
      begin: GEN_REGS
        ccs_genreg_v1
        #(
          .width   (1),
          .ph_clk  (ph_clk),
          .ph_en   (ph_en),
          .ph_arst (ph_arst),
          .ph_srst (ph_srst),
          .has_en  (1'b1)
        )
        STATREG
        (
          .clk     (clk),
          .en      (en_l_s[eni/8]),
          .arst    (arst),
          .srst    (srst),
          .d       (stat_pre[eni]),
          .z       (stat[eni])
        );

        ccs_genreg_v1
        #(
          .width   (width),
          .ph_clk  (ph_clk),
          .ph_en   (ph_en),
          .ph_arst (ph_arst),
          .ph_srst (ph_srst),
          .has_en  (1'b1)
        )
        BUFREG
        (
          .clk     (clk),
          .en      (en_l[eni]),
          .arst    (arst),
          .srst    (srst),
          .d       (buff_pre[width*eni+:width]),
          .z       (buff[width*eni+:width])
        );
      end

    end
    else
    begin: FEED_THRU
      assign din_rdy_drv  = dout_rdy;
      assign dout_vld_drv = din_vld;
      assign dout     = din;
      // non-blocking is not II=1 when fifo_sz=0
      assign sd = {{(sz_width-1){1'b0}}, (din_vld & ~dout_rdy)};
      assign is_idle_drv = ~(din_vld & dout_rdy);
    end
    endgenerate

`ifdef RDY_ASRT
    generate
    if (ph_clk==1)
    begin: POS_CLK_ASSERT

       property rdyAsrt ;
         @(posedge clk) (srst==ph_srst) |=> (din_rdy==0);
       endproperty
       a1Pos: assert property(rdyAsrt);

       property rdyAsrtASync ;
         @(posedge clk) (arst==ph_arst) |-> (din_rdy==0);
       endproperty
       a2Pos: assert property(rdyAsrtASync);

    end else if (ph_clk==0)
    begin: NEG_CLK_ASSERT

       property rdyAsrt ;
         @(negedge clk) ((srst==ph_srst) || (arst==ph_arst)) |=> (din_rdy==0);
       endproperty
       a1Neg: assert property(rdyAsrt);

       property rdyAsrtASync ;
         @(negedge clk) (arst==ph_arst) |-> (din_rdy==0);
       endproperty
       a2Neg: assert property(rdyAsrtASync);

    end
    endgenerate
`endif

endmodule

//------> /usr/cadtool/mentor/Catapult/2024.1/Mgc_home/pkgs/siflibs/ccs_pipe_v6.v 
//------------------------------------------------------------------------------
// Catapult Synthesis - Sample I/O Port Library
//
// Copyright (c) 2003-2017 Mentor Graphics Corp.
//       All Rights Reserved
//
// This document may be used and distributed without restriction provided that
// this copyright statement is not removed from the file and that any derivative
// work contains this copyright notice.
//
// The design information contained in this file is intended to be an example
// of the functionality which the end user may study in preparation for creating
// their own custom interfaces. This design does not necessarily present a 
// complete implementation of the named protocol or standard.
//
//------------------------------------------------------------------------------
/*
 *
 *            _______________________________________________
 * WRITER    |                                              |          READER
 *           |                 ccs_pipe                     |
 *           |            ______________________            |
 *        --<| din_rdy --<|  ---------------- <|---dout_rdy<|---
 *           |            |       FIFO         |            |
 *        ---|>din_vld ---|> ----------------  |>--dout_vld |>--
 *        ---|>din -------|> ----------------  |> -----dout |>--
 *           |            |____________________|            |
 *           |______________________________________________|
 *
 *    din_rdy     - can be considered as a notFULL signal
 *    dout_vld    - can be considered as a notEMPTY signal
 *    write_stall - an internal debug signal formed from din_vld & !din_rdy
 *    read_stall  - an internal debug signal formed from dout_rdy & !dout_vld
 *    is_idle     - indicates the clock can be safely gated
 *    stall_ctrl  - Stall the pipe(fifo).  Used by STALL_FLAG_SV directive
 */

module ccs_pipe_v6 (clk, en, arst, srst, din_rdy, din_vld, din, dout_rdy, dout_vld, dout, 
                    sz, sz_req, is_idle);

    parameter integer rscid    = 0; // resource ID
    parameter integer width    = 8; // fifo width
    parameter integer sz_width = 8; // width of size of elements in fifo
    parameter integer fifo_sz  = 8; // fifo depth
    parameter integer log2_sz  = 3; // log2(fifo_sz)
    parameter integer ph_clk   = 1; // clock polarity 1=rising edge, 0=falling edge
    parameter integer ph_en    = 1; // clock enable polarity
    parameter integer ph_arst  = 1; // async reset polarity
    parameter integer ph_srst  = 1; // sync reset polarity

    // clock 
    input              clk;
    input              en;
    input              arst;
    input              srst;

    // writer
    output             din_rdy;
    input              din_vld;
    input  [width-1:0] din;

    // reader
    input              dout_rdy;
    output             dout_vld;
    output [width-1:0] dout;

    // size
    output [sz_width-1:0] sz;
    input                 sz_req;
    output                is_idle;

    localparam stallOff = 0; 
    wire                  stall_ctrl;
    assign stall_ctrl = stallOff;
   
    // synopsys translate_off
    wire   write_stall;
    wire   read_stall;
    assign write_stall = (din_vld & !din_rdy) | stall_ctrl;
    assign read_stall  = (dout_rdy & !dout_vld) | stall_ctrl;
    // synopsys translate_on

    wire    tmp_din_rdy;
    assign  din_rdy = tmp_din_rdy & !stall_ctrl;
    wire    tmp_dout_vld;
    assign  dout_vld = tmp_dout_vld & !stall_ctrl;
   
    ccs_fifo_wait_core_v5
    #(
        .rscid    (rscid),
        .width    (width),
        .sz_width (sz_width),
        .fifo_sz  (fifo_sz),
        .ph_clk   (ph_clk),
        .ph_en    (ph_en),
        .ph_arst  (ph_arst),
        .ph_srst  (ph_srst),
        .ph_log2  (log2_sz)
    )
    FIFO
    (
        .clk      (clk),
        .en       (en),
        .arst     (arst),
        .srst     (srst),
        .din_vld  (din_vld & !stall_ctrl),
        .din_rdy  (tmp_din_rdy),
        .din      (din),
        .dout_vld (tmp_dout_vld),
        .dout_rdy (dout_rdy & !stall_ctrl),
        .dout     (dout),
        .sd       (sz),
        .is_idle  (is_idle)
    );

endmodule


//------> ./rtl.v 
// ----------------------------------------------------------------------
//  HLS HDL:        Verilog Netlister
//  HLS Version:    2024.1/1091966 Production Release
//  HLS Date:       Wed Feb 14 09:07:18 PST 2024
// 
//  Generated by:   m111061605@ws34
//  Generated date: Sat Apr 13 15:03:49 2024
// ----------------------------------------------------------------------

// 
// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_Xilinx_RAMS_BLOCK_1R1W_RBW_rwport_en_7_7_64_80_1_80_64_1_gen
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_Xilinx_RAMS_BLOCK_1R1W_RBW_rwport_en_7_7_64_80_1_80_64_1_gen
    (
  clken, q, re, radr, we, d, wadr, clken_d, d_d, q_d, radr_d, re_d, wadr_d, we_d,
      writeA_w_ram_ir_internal_WMASK_B_d, readA_r_ram_ir_internal_RMASK_B_d
);
  output clken;
  input [63:0] q;
  output re;
  output [6:0] radr;
  output we;
  output [63:0] d;
  output [6:0] wadr;
  input clken_d;
  input [63:0] d_d;
  output [63:0] q_d;
  input [6:0] radr_d;
  input re_d;
  input [6:0] wadr_d;
  input we_d;
  input writeA_w_ram_ir_internal_WMASK_B_d;
  input readA_r_ram_ir_internal_RMASK_B_d;



  // Interconnect Declarations for Component Instantiations 
  assign clken = (clken_d);
  assign q_d = q;
  assign re = (readA_r_ram_ir_internal_RMASK_B_d);
  assign radr = (radr_d);
  assign we = (writeA_w_ram_ir_internal_WMASK_B_d);
  assign d = (d_d);
  assign wadr = (wadr_d);
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_Xilinx_RAMS_BLOCK_1R1W_RBW_rwport_en_6_7_64_80_1_80_64_1_gen
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_Xilinx_RAMS_BLOCK_1R1W_RBW_rwport_en_6_7_64_80_1_80_64_1_gen
    (
  clken, q, re, radr, we, d, wadr, clken_d, d_d, q_d, radr_d, re_d, wadr_d, we_d,
      writeA_w_ram_ir_internal_WMASK_B_d, readA_r_ram_ir_internal_RMASK_B_d
);
  output clken;
  input [63:0] q;
  output re;
  output [6:0] radr;
  output we;
  output [63:0] d;
  output [6:0] wadr;
  input clken_d;
  input [63:0] d_d;
  output [63:0] q_d;
  input [6:0] radr_d;
  input re_d;
  input [6:0] wadr_d;
  input we_d;
  input writeA_w_ram_ir_internal_WMASK_B_d;
  input readA_r_ram_ir_internal_RMASK_B_d;



  // Interconnect Declarations for Component Instantiations 
  assign clken = (clken_d);
  assign q_d = q;
  assign re = (readA_r_ram_ir_internal_RMASK_B_d);
  assign radr = (radr_d);
  assign we = (writeA_w_ram_ir_internal_WMASK_B_d);
  assign d = (d_d);
  assign wadr = (wadr_d);
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_run_run_fsm
//  FSM Module
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_run_run_fsm (
  clk, rst, arst_n, run_wen, fsm_output, VCOL_C_0_tr0, VROW_C_0_tr0
);
  input clk;
  input rst;
  input arst_n;
  input run_wen;
  output [3:0] fsm_output;
  reg [3:0] fsm_output;
  input VCOL_C_0_tr0;
  input VROW_C_0_tr0;


  // FSM State Type Declaration for EdgeDetect_IP_EdgeDetect_VerDer_run_run_fsm_1
  parameter
    main_C_0 = 2'd0,
    VCOL_C_0 = 2'd1,
    VROW_C_0 = 2'd2,
    main_C_1 = 2'd3;

  reg [1:0] state_var;
  reg [1:0] state_var_NS;


  // Interconnect Declarations for Component Instantiations 
  always @(*)
  begin : EdgeDetect_IP_EdgeDetect_VerDer_run_run_fsm_1
    case (state_var)
      VCOL_C_0 : begin
        fsm_output = 4'b0010;
        if ( VCOL_C_0_tr0 ) begin
          state_var_NS = VROW_C_0;
        end
        else begin
          state_var_NS = VCOL_C_0;
        end
      end
      VROW_C_0 : begin
        fsm_output = 4'b0100;
        if ( VROW_C_0_tr0 ) begin
          state_var_NS = main_C_1;
        end
        else begin
          state_var_NS = VCOL_C_0;
        end
      end
      main_C_1 : begin
        fsm_output = 4'b1000;
        state_var_NS = main_C_0;
      end
      // main_C_0
      default : begin
        fsm_output = 4'b0001;
        state_var_NS = VCOL_C_0;
      end
    endcase
  end

  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      state_var <= main_C_0;
    end
    else if ( rst ) begin
      state_var <= main_C_0;
    end
    else if ( run_wen ) begin
      state_var <= state_var_NS;
    end
  end

endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_run_staller
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_run_staller (
  clk, rst, arst_n, run_wen, run_wten, dat_in_rsci_wen_comp, pix_chan1_rsci_wen_comp,
      dy_chan_rsci_wen_comp, run_flen_unreg
);
  input clk;
  input rst;
  input arst_n;
  output run_wen;
  output run_wten;
  input dat_in_rsci_wen_comp;
  input pix_chan1_rsci_wen_comp;
  input dy_chan_rsci_wen_comp;
  input run_flen_unreg;


  // Interconnect Declarations
  reg run_wten_reg;


  // Interconnect Declarations for Component Instantiations 
  assign run_wen = dat_in_rsci_wen_comp & pix_chan1_rsci_wen_comp & dy_chan_rsci_wen_comp
      & (~ run_flen_unreg);
  assign run_wten = run_wten_reg;
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      run_wten_reg <= 1'b0;
    end
    else if ( rst ) begin
      run_wten_reg <= 1'b0;
    end
    else begin
      run_wten_reg <= ~ run_wen;
    end
  end
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf1_rsci_1_line_buf1_rsc_wait_dp
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf1_rsci_1_line_buf1_rsc_wait_dp
    (
  clk, rst, arst_n, line_buf1_rsci_q_d, line_buf1_rsci_bawt, line_buf1_rsci_q_d_mxwt,
      line_buf1_rsci_biwt, line_buf1_rsci_bdwt
);
  input clk;
  input rst;
  input arst_n;
  input [63:0] line_buf1_rsci_q_d;
  output line_buf1_rsci_bawt;
  output [63:0] line_buf1_rsci_q_d_mxwt;
  input line_buf1_rsci_biwt;
  input line_buf1_rsci_bdwt;


  // Interconnect Declarations
  reg line_buf1_rsci_bcwt;
  reg [63:0] line_buf1_rsci_q_d_bfwt;


  // Interconnect Declarations for Component Instantiations 
  assign line_buf1_rsci_bawt = line_buf1_rsci_biwt | line_buf1_rsci_bcwt;
  assign line_buf1_rsci_q_d_mxwt = MUX_v_64_2_2(line_buf1_rsci_q_d, line_buf1_rsci_q_d_bfwt,
      line_buf1_rsci_bcwt);
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      line_buf1_rsci_bcwt <= 1'b0;
    end
    else if ( rst ) begin
      line_buf1_rsci_bcwt <= 1'b0;
    end
    else begin
      line_buf1_rsci_bcwt <= ~((~(line_buf1_rsci_bcwt | line_buf1_rsci_biwt)) | line_buf1_rsci_bdwt);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      line_buf1_rsci_q_d_bfwt <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
    end
    else if ( rst ) begin
      line_buf1_rsci_q_d_bfwt <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
    end
    else if ( line_buf1_rsci_biwt ) begin
      line_buf1_rsci_q_d_bfwt <= line_buf1_rsci_q_d;
    end
  end

  function automatic [63:0] MUX_v_64_2_2;
    input [63:0] input_0;
    input [63:0] input_1;
    input  sel;
    reg [63:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_64_2_2 = result;
  end
  endfunction

endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf1_rsci_1_line_buf1_rsc_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf1_rsci_1_line_buf1_rsc_wait_ctrl
    (
  run_wen, run_wten, line_buf1_rsci_oswt_unreg, line_buf1_rsci_iswt0, line_buf1_rsci_biwt,
      line_buf1_rsci_bdwt, line_buf1_rsci_re_d_run_sct_pff, line_buf1_rsci_iswt0_pff,
      line_buf1_rsci_we_d_run_sct_pff, line_buf1_rsci_iswt0_1_pff
);
  input run_wen;
  input run_wten;
  input line_buf1_rsci_oswt_unreg;
  input line_buf1_rsci_iswt0;
  output line_buf1_rsci_biwt;
  output line_buf1_rsci_bdwt;
  output line_buf1_rsci_re_d_run_sct_pff;
  input line_buf1_rsci_iswt0_pff;
  output line_buf1_rsci_we_d_run_sct_pff;
  input line_buf1_rsci_iswt0_1_pff;



  // Interconnect Declarations for Component Instantiations 
  assign line_buf1_rsci_bdwt = line_buf1_rsci_oswt_unreg & run_wen;
  assign line_buf1_rsci_biwt = (~ run_wten) & line_buf1_rsci_iswt0;
  assign line_buf1_rsci_re_d_run_sct_pff = line_buf1_rsci_iswt0_pff & run_wen;
  assign line_buf1_rsci_we_d_run_sct_pff = line_buf1_rsci_iswt0_1_pff & run_wen;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf0_rsci_1_line_buf0_rsc_wait_dp
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf0_rsci_1_line_buf0_rsc_wait_dp
    (
  clk, rst, arst_n, line_buf0_rsci_q_d, line_buf0_rsci_bawt, line_buf0_rsci_q_d_mxwt,
      line_buf0_rsci_biwt, line_buf0_rsci_bdwt
);
  input clk;
  input rst;
  input arst_n;
  input [63:0] line_buf0_rsci_q_d;
  output line_buf0_rsci_bawt;
  output [63:0] line_buf0_rsci_q_d_mxwt;
  input line_buf0_rsci_biwt;
  input line_buf0_rsci_bdwt;


  // Interconnect Declarations
  reg line_buf0_rsci_bcwt;
  reg [63:0] line_buf0_rsci_q_d_bfwt;


  // Interconnect Declarations for Component Instantiations 
  assign line_buf0_rsci_bawt = line_buf0_rsci_biwt | line_buf0_rsci_bcwt;
  assign line_buf0_rsci_q_d_mxwt = MUX_v_64_2_2(line_buf0_rsci_q_d, line_buf0_rsci_q_d_bfwt,
      line_buf0_rsci_bcwt);
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      line_buf0_rsci_bcwt <= 1'b0;
    end
    else if ( rst ) begin
      line_buf0_rsci_bcwt <= 1'b0;
    end
    else begin
      line_buf0_rsci_bcwt <= ~((~(line_buf0_rsci_bcwt | line_buf0_rsci_biwt)) | line_buf0_rsci_bdwt);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      line_buf0_rsci_q_d_bfwt <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
    end
    else if ( rst ) begin
      line_buf0_rsci_q_d_bfwt <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
    end
    else if ( line_buf0_rsci_biwt ) begin
      line_buf0_rsci_q_d_bfwt <= line_buf0_rsci_q_d;
    end
  end

  function automatic [63:0] MUX_v_64_2_2;
    input [63:0] input_0;
    input [63:0] input_1;
    input  sel;
    reg [63:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_64_2_2 = result;
  end
  endfunction

endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf0_rsci_1_line_buf0_rsc_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf0_rsci_1_line_buf0_rsc_wait_ctrl
    (
  run_wen, run_wten, line_buf0_rsci_oswt_unreg, line_buf0_rsci_iswt0, line_buf0_rsci_biwt,
      line_buf0_rsci_bdwt, line_buf0_rsci_re_d_run_sct_pff, line_buf0_rsci_iswt0_pff,
      line_buf0_rsci_we_d_run_sct_pff, line_buf0_rsci_iswt0_1_pff
);
  input run_wen;
  input run_wten;
  input line_buf0_rsci_oswt_unreg;
  input line_buf0_rsci_iswt0;
  output line_buf0_rsci_biwt;
  output line_buf0_rsci_bdwt;
  output line_buf0_rsci_re_d_run_sct_pff;
  input line_buf0_rsci_iswt0_pff;
  output line_buf0_rsci_we_d_run_sct_pff;
  input line_buf0_rsci_iswt0_1_pff;



  // Interconnect Declarations for Component Instantiations 
  assign line_buf0_rsci_bdwt = line_buf0_rsci_oswt_unreg & run_wen;
  assign line_buf0_rsci_biwt = (~ run_wten) & line_buf0_rsci_iswt0;
  assign line_buf0_rsci_re_d_run_sct_pff = line_buf0_rsci_iswt0_pff & run_wen;
  assign line_buf0_rsci_we_d_run_sct_pff = line_buf0_rsci_iswt0_1_pff & run_wen;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_run_dy_chan_rsci_dy_chan_wait_dp
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_run_dy_chan_rsci_dy_chan_wait_dp (
  clk, rst, arst_n, dy_chan_rsci_oswt_unreg, dy_chan_rsci_bawt, dy_chan_rsci_wen_comp,
      dy_chan_rsci_biwt, dy_chan_rsci_bdwt, dy_chan_rsci_bcwt
);
  input clk;
  input rst;
  input arst_n;
  input dy_chan_rsci_oswt_unreg;
  output dy_chan_rsci_bawt;
  output dy_chan_rsci_wen_comp;
  input dy_chan_rsci_biwt;
  input dy_chan_rsci_bdwt;
  output dy_chan_rsci_bcwt;
  reg dy_chan_rsci_bcwt;



  // Interconnect Declarations for Component Instantiations 
  assign dy_chan_rsci_bawt = dy_chan_rsci_biwt | dy_chan_rsci_bcwt;
  assign dy_chan_rsci_wen_comp = (~ dy_chan_rsci_oswt_unreg) | dy_chan_rsci_bawt;
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      dy_chan_rsci_bcwt <= 1'b0;
    end
    else if ( rst ) begin
      dy_chan_rsci_bcwt <= 1'b0;
    end
    else begin
      dy_chan_rsci_bcwt <= ~((~(dy_chan_rsci_bcwt | dy_chan_rsci_biwt)) | dy_chan_rsci_bdwt);
    end
  end
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_run_dy_chan_rsci_dy_chan_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_run_dy_chan_rsci_dy_chan_wait_ctrl (
  run_wen, dy_chan_rsci_oswt_unreg, dy_chan_rsci_iswt0, dy_chan_rsci_biwt, dy_chan_rsci_bdwt,
      dy_chan_rsci_bcwt, dy_chan_rsci_irdy, dy_chan_rsci_ivld_run_sct
);
  input run_wen;
  input dy_chan_rsci_oswt_unreg;
  input dy_chan_rsci_iswt0;
  output dy_chan_rsci_biwt;
  output dy_chan_rsci_bdwt;
  input dy_chan_rsci_bcwt;
  input dy_chan_rsci_irdy;
  output dy_chan_rsci_ivld_run_sct;


  // Interconnect Declarations
  wire dy_chan_rsci_ogwt;


  // Interconnect Declarations for Component Instantiations 
  assign dy_chan_rsci_bdwt = dy_chan_rsci_oswt_unreg & run_wen;
  assign dy_chan_rsci_biwt = dy_chan_rsci_ogwt & dy_chan_rsci_irdy;
  assign dy_chan_rsci_ogwt = dy_chan_rsci_iswt0 & (~ dy_chan_rsci_bcwt);
  assign dy_chan_rsci_ivld_run_sct = dy_chan_rsci_ogwt;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_run_pix_chan1_rsci_pix_chan1_wait_dp
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_run_pix_chan1_rsci_pix_chan1_wait_dp (
  clk, rst, arst_n, pix_chan1_rsci_oswt_unreg, pix_chan1_rsci_bawt, pix_chan1_rsci_wen_comp,
      pix_chan1_rsci_biwt, pix_chan1_rsci_bdwt, pix_chan1_rsci_bcwt
);
  input clk;
  input rst;
  input arst_n;
  input pix_chan1_rsci_oswt_unreg;
  output pix_chan1_rsci_bawt;
  output pix_chan1_rsci_wen_comp;
  input pix_chan1_rsci_biwt;
  input pix_chan1_rsci_bdwt;
  output pix_chan1_rsci_bcwt;
  reg pix_chan1_rsci_bcwt;



  // Interconnect Declarations for Component Instantiations 
  assign pix_chan1_rsci_bawt = pix_chan1_rsci_biwt | pix_chan1_rsci_bcwt;
  assign pix_chan1_rsci_wen_comp = (~ pix_chan1_rsci_oswt_unreg) | pix_chan1_rsci_bawt;
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_chan1_rsci_bcwt <= 1'b0;
    end
    else if ( rst ) begin
      pix_chan1_rsci_bcwt <= 1'b0;
    end
    else begin
      pix_chan1_rsci_bcwt <= ~((~(pix_chan1_rsci_bcwt | pix_chan1_rsci_biwt)) | pix_chan1_rsci_bdwt);
    end
  end
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_run_pix_chan1_rsci_pix_chan1_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_run_pix_chan1_rsci_pix_chan1_wait_ctrl (
  run_wen, pix_chan1_rsci_oswt_unreg, pix_chan1_rsci_iswt0, pix_chan1_rsci_biwt,
      pix_chan1_rsci_bdwt, pix_chan1_rsci_bcwt, pix_chan1_rsci_irdy, pix_chan1_rsci_ivld_run_sct
);
  input run_wen;
  input pix_chan1_rsci_oswt_unreg;
  input pix_chan1_rsci_iswt0;
  output pix_chan1_rsci_biwt;
  output pix_chan1_rsci_bdwt;
  input pix_chan1_rsci_bcwt;
  input pix_chan1_rsci_irdy;
  output pix_chan1_rsci_ivld_run_sct;


  // Interconnect Declarations
  wire pix_chan1_rsci_ogwt;


  // Interconnect Declarations for Component Instantiations 
  assign pix_chan1_rsci_bdwt = pix_chan1_rsci_oswt_unreg & run_wen;
  assign pix_chan1_rsci_biwt = pix_chan1_rsci_ogwt & pix_chan1_rsci_irdy;
  assign pix_chan1_rsci_ogwt = pix_chan1_rsci_iswt0 & (~ pix_chan1_rsci_bcwt);
  assign pix_chan1_rsci_ivld_run_sct = pix_chan1_rsci_ogwt;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_run_dat_in_rsci_dat_in_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_run_dat_in_rsci_dat_in_wait_ctrl (
  run_wen, dat_in_rsci_oswt_unreg, dat_in_rsci_iswt0, dat_in_rsci_irdy_run_sct
);
  input run_wen;
  input dat_in_rsci_oswt_unreg;
  input dat_in_rsci_iswt0;
  output dat_in_rsci_irdy_run_sct;



  // Interconnect Declarations for Component Instantiations 
  assign dat_in_rsci_irdy_run_sct = dat_in_rsci_iswt0 & run_wen & dat_in_rsci_oswt_unreg;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_HorDer_run_run_fsm
//  FSM Module
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_HorDer_run_run_fsm (
  clk, rst, arst_n, run_wen, fsm_output, HCOL_C_2_tr0, HROW_C_0_tr0
);
  input clk;
  input rst;
  input arst_n;
  input run_wen;
  output [5:0] fsm_output;
  reg [5:0] fsm_output;
  input HCOL_C_2_tr0;
  input HROW_C_0_tr0;


  // FSM State Type Declaration for EdgeDetect_IP_EdgeDetect_HorDer_run_run_fsm_1
  parameter
    main_C_0 = 3'd0,
    HCOL_C_0 = 3'd1,
    HCOL_C_1 = 3'd2,
    HCOL_C_2 = 3'd3,
    HROW_C_0 = 3'd4,
    main_C_1 = 3'd5;

  reg [2:0] state_var;
  reg [2:0] state_var_NS;


  // Interconnect Declarations for Component Instantiations 
  always @(*)
  begin : EdgeDetect_IP_EdgeDetect_HorDer_run_run_fsm_1
    case (state_var)
      HCOL_C_0 : begin
        fsm_output = 6'b000010;
        state_var_NS = HCOL_C_1;
      end
      HCOL_C_1 : begin
        fsm_output = 6'b000100;
        state_var_NS = HCOL_C_2;
      end
      HCOL_C_2 : begin
        fsm_output = 6'b001000;
        if ( HCOL_C_2_tr0 ) begin
          state_var_NS = HROW_C_0;
        end
        else begin
          state_var_NS = HCOL_C_0;
        end
      end
      HROW_C_0 : begin
        fsm_output = 6'b010000;
        if ( HROW_C_0_tr0 ) begin
          state_var_NS = main_C_1;
        end
        else begin
          state_var_NS = HCOL_C_0;
        end
      end
      main_C_1 : begin
        fsm_output = 6'b100000;
        state_var_NS = main_C_0;
      end
      // main_C_0
      default : begin
        fsm_output = 6'b000001;
        state_var_NS = HCOL_C_0;
      end
    endcase
  end

  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      state_var <= main_C_0;
    end
    else if ( rst ) begin
      state_var <= main_C_0;
    end
    else if ( run_wen ) begin
      state_var <= state_var_NS;
    end
  end

endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_HorDer_run_staller
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_HorDer_run_staller (
  run_wen, pix_chan1_rsci_wen_comp, pix_chan2_rsci_wen_comp, dx_chan_rsci_wen_comp
);
  output run_wen;
  input pix_chan1_rsci_wen_comp;
  input pix_chan2_rsci_wen_comp;
  input dx_chan_rsci_wen_comp;



  // Interconnect Declarations for Component Instantiations 
  assign run_wen = pix_chan1_rsci_wen_comp & pix_chan2_rsci_wen_comp & dx_chan_rsci_wen_comp;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_HorDer_run_dx_chan_rsci_dx_chan_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_HorDer_run_dx_chan_rsci_dx_chan_wait_ctrl (
  dx_chan_rsci_iswt0, dx_chan_rsci_biwt, dx_chan_rsci_irdy
);
  input dx_chan_rsci_iswt0;
  output dx_chan_rsci_biwt;
  input dx_chan_rsci_irdy;



  // Interconnect Declarations for Component Instantiations 
  assign dx_chan_rsci_biwt = dx_chan_rsci_iswt0 & dx_chan_rsci_irdy;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_HorDer_run_pix_chan2_rsci_pix_chan2_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_HorDer_run_pix_chan2_rsci_pix_chan2_wait_ctrl (
  pix_chan2_rsci_iswt0, pix_chan2_rsci_biwt, pix_chan2_rsci_irdy
);
  input pix_chan2_rsci_iswt0;
  output pix_chan2_rsci_biwt;
  input pix_chan2_rsci_irdy;



  // Interconnect Declarations for Component Instantiations 
  assign pix_chan2_rsci_biwt = pix_chan2_rsci_iswt0 & pix_chan2_rsci_irdy;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_HorDer_run_pix_chan1_rsci_pix_chan1_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_HorDer_run_pix_chan1_rsci_pix_chan1_wait_ctrl (
  pix_chan1_rsci_iswt0, pix_chan1_rsci_biwt, pix_chan1_rsci_ivld
);
  input pix_chan1_rsci_iswt0;
  output pix_chan1_rsci_biwt;
  input pix_chan1_rsci_ivld;



  // Interconnect Declarations for Component Instantiations 
  assign pix_chan1_rsci_biwt = pix_chan1_rsci_iswt0 & pix_chan1_rsci_ivld;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_run_fsm
//  FSM Module
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_run_fsm (
  clk, rst, arst_n, run_wen, fsm_output, MCOL_C_1_tr0, MROW_C_0_tr0
);
  input clk;
  input rst;
  input arst_n;
  input run_wen;
  output [6:0] fsm_output;
  reg [6:0] fsm_output;
  input MCOL_C_1_tr0;
  input MROW_C_0_tr0;


  // FSM State Type Declaration for EdgeDetect_IP_EdgeDetect_MagAng_run_run_fsm_1
  parameter
    run_rlp_C_0 = 3'd0,
    run_rlp_C_1 = 3'd1,
    main_C_0 = 3'd2,
    MCOL_C_0 = 3'd3,
    MCOL_C_1 = 3'd4,
    MROW_C_0 = 3'd5,
    main_C_1 = 3'd6;

  reg [2:0] state_var;
  reg [2:0] state_var_NS;


  // Interconnect Declarations for Component Instantiations 
  always @(*)
  begin : EdgeDetect_IP_EdgeDetect_MagAng_run_run_fsm_1
    case (state_var)
      run_rlp_C_1 : begin
        fsm_output = 7'b0000010;
        state_var_NS = main_C_0;
      end
      main_C_0 : begin
        fsm_output = 7'b0000100;
        state_var_NS = MCOL_C_0;
      end
      MCOL_C_0 : begin
        fsm_output = 7'b0001000;
        state_var_NS = MCOL_C_1;
      end
      MCOL_C_1 : begin
        fsm_output = 7'b0010000;
        if ( MCOL_C_1_tr0 ) begin
          state_var_NS = MROW_C_0;
        end
        else begin
          state_var_NS = MCOL_C_0;
        end
      end
      MROW_C_0 : begin
        fsm_output = 7'b0100000;
        if ( MROW_C_0_tr0 ) begin
          state_var_NS = main_C_1;
        end
        else begin
          state_var_NS = MCOL_C_0;
        end
      end
      main_C_1 : begin
        fsm_output = 7'b1000000;
        state_var_NS = main_C_0;
      end
      // run_rlp_C_0
      default : begin
        fsm_output = 7'b0000001;
        state_var_NS = run_rlp_C_1;
      end
    endcase
  end

  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      state_var <= run_rlp_C_0;
    end
    else if ( rst ) begin
      state_var <= run_rlp_C_0;
    end
    else if ( run_wen ) begin
      state_var <= state_var_NS;
    end
  end

endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_staller
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_staller (
  clk, rst, arst_n, run_wen, run_wten, dx_chan_rsci_wen_comp, dy_chan_rsci_wen_comp,
      pix_chan2_rsci_wen_comp, dat_out_rsci_wen_comp
);
  input clk;
  input rst;
  input arst_n;
  output run_wen;
  output run_wten;
  input dx_chan_rsci_wen_comp;
  input dy_chan_rsci_wen_comp;
  input pix_chan2_rsci_wen_comp;
  input dat_out_rsci_wen_comp;


  // Interconnect Declarations
  reg run_wten_reg;


  // Interconnect Declarations for Component Instantiations 
  assign run_wen = dx_chan_rsci_wen_comp & dy_chan_rsci_wen_comp & pix_chan2_rsci_wen_comp
      & dat_out_rsci_wen_comp;
  assign run_wten = run_wten_reg;
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      run_wten_reg <= 1'b0;
    end
    else if ( rst ) begin
      run_wten_reg <= 1'b0;
    end
    else begin
      run_wten_reg <= ~ run_wen;
    end
  end
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_triosy_obj_crc32_dat_out_triosy_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_triosy_obj_crc32_dat_out_triosy_wait_ctrl
    (
  run_wten, crc32_dat_out_triosy_obj_iswt0, crc32_dat_out_triosy_obj_biwt
);
  input run_wten;
  input crc32_dat_out_triosy_obj_iswt0;
  output crc32_dat_out_triosy_obj_biwt;



  // Interconnect Declarations for Component Instantiations 
  assign crc32_dat_out_triosy_obj_biwt = (~ run_wten) & crc32_dat_out_triosy_obj_iswt0;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_triosy_obj_crc32_pix_in_triosy_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_triosy_obj_crc32_pix_in_triosy_wait_ctrl
    (
  run_wten, crc32_pix_in_triosy_obj_iswt0, crc32_pix_in_triosy_obj_biwt
);
  input run_wten;
  input crc32_pix_in_triosy_obj_iswt0;
  output crc32_pix_in_triosy_obj_biwt;



  // Interconnect Declarations for Component Instantiations 
  assign crc32_pix_in_triosy_obj_biwt = (~ run_wten) & crc32_pix_in_triosy_obj_iswt0;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_sw_in_triosy_obj_sw_in_triosy_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_sw_in_triosy_obj_sw_in_triosy_wait_ctrl
    (
  run_wten, sw_in_triosy_obj_iswt0, sw_in_triosy_obj_biwt
);
  input run_wten;
  input sw_in_triosy_obj_iswt0;
  output sw_in_triosy_obj_biwt;



  // Interconnect Declarations for Component Instantiations 
  assign sw_in_triosy_obj_biwt = (~ run_wten) & sw_in_triosy_obj_iswt0;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_dat_out_rsci_dat_out_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_dat_out_rsci_dat_out_wait_ctrl (
  dat_out_rsci_iswt0, dat_out_rsci_biwt, dat_out_rsci_irdy
);
  input dat_out_rsci_iswt0;
  output dat_out_rsci_biwt;
  input dat_out_rsci_irdy;



  // Interconnect Declarations for Component Instantiations 
  assign dat_out_rsci_biwt = dat_out_rsci_iswt0 & dat_out_rsci_irdy;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_rsci_crc32_dat_out_rsc_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_rsci_crc32_dat_out_rsc_wait_ctrl
    (
  run_wten, crc32_dat_out_rsci_iswt0, crc32_dat_out_rsci_ldout_run_sct
);
  input run_wten;
  input crc32_dat_out_rsci_iswt0;
  output crc32_dat_out_rsci_ldout_run_sct;



  // Interconnect Declarations for Component Instantiations 
  assign crc32_dat_out_rsci_ldout_run_sct = crc32_dat_out_rsci_iswt0 & (~ run_wten);
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_rsci_crc32_pix_in_rsc_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_rsci_crc32_pix_in_rsc_wait_ctrl
    (
  run_wten, crc32_pix_in_rsci_iswt0, crc32_pix_in_rsci_ldout_run_sct
);
  input run_wten;
  input crc32_pix_in_rsci_iswt0;
  output crc32_pix_in_rsci_ldout_run_sct;



  // Interconnect Declarations for Component Instantiations 
  assign crc32_pix_in_rsci_ldout_run_sct = crc32_pix_in_rsci_iswt0 & (~ run_wten);
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_pix_chan2_rsci_pix_chan2_wait_dp
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_pix_chan2_rsci_pix_chan2_wait_dp (
  clk, rst, arst_n, pix_chan2_rsci_oswt, pix_chan2_rsci_wen_comp, pix_chan2_rsci_idat_mxwt,
      pix_chan2_rsci_biwt, pix_chan2_rsci_bdwt, pix_chan2_rsci_bcwt, pix_chan2_rsci_idat
);
  input clk;
  input rst;
  input arst_n;
  input pix_chan2_rsci_oswt;
  output pix_chan2_rsci_wen_comp;
  output [31:0] pix_chan2_rsci_idat_mxwt;
  input pix_chan2_rsci_biwt;
  input pix_chan2_rsci_bdwt;
  output pix_chan2_rsci_bcwt;
  reg pix_chan2_rsci_bcwt;
  input [31:0] pix_chan2_rsci_idat;


  // Interconnect Declarations
  reg [31:0] pix_chan2_rsci_idat_bfwt;


  // Interconnect Declarations for Component Instantiations 
  assign pix_chan2_rsci_wen_comp = (~ pix_chan2_rsci_oswt) | pix_chan2_rsci_biwt
      | pix_chan2_rsci_bcwt;
  assign pix_chan2_rsci_idat_mxwt = MUX_v_32_2_2(pix_chan2_rsci_idat, pix_chan2_rsci_idat_bfwt,
      pix_chan2_rsci_bcwt);
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_chan2_rsci_bcwt <= 1'b0;
    end
    else if ( rst ) begin
      pix_chan2_rsci_bcwt <= 1'b0;
    end
    else begin
      pix_chan2_rsci_bcwt <= ~((~(pix_chan2_rsci_bcwt | pix_chan2_rsci_biwt)) | pix_chan2_rsci_bdwt);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_chan2_rsci_idat_bfwt <= 32'b00000000000000000000000000000000;
    end
    else if ( rst ) begin
      pix_chan2_rsci_idat_bfwt <= 32'b00000000000000000000000000000000;
    end
    else if ( pix_chan2_rsci_biwt ) begin
      pix_chan2_rsci_idat_bfwt <= pix_chan2_rsci_idat;
    end
  end

  function automatic [31:0] MUX_v_32_2_2;
    input [31:0] input_0;
    input [31:0] input_1;
    input  sel;
    reg [31:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_32_2_2 = result;
  end
  endfunction

endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_pix_chan2_rsci_pix_chan2_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_pix_chan2_rsci_pix_chan2_wait_ctrl (
  run_wen, pix_chan2_rsci_oswt, pix_chan2_rsci_biwt, pix_chan2_rsci_bdwt, pix_chan2_rsci_bcwt,
      pix_chan2_rsci_irdy_run_sct, pix_chan2_rsci_ivld
);
  input run_wen;
  input pix_chan2_rsci_oswt;
  output pix_chan2_rsci_biwt;
  output pix_chan2_rsci_bdwt;
  input pix_chan2_rsci_bcwt;
  output pix_chan2_rsci_irdy_run_sct;
  input pix_chan2_rsci_ivld;


  // Interconnect Declarations
  wire pix_chan2_rsci_ogwt;


  // Interconnect Declarations for Component Instantiations 
  assign pix_chan2_rsci_bdwt = pix_chan2_rsci_oswt & run_wen;
  assign pix_chan2_rsci_biwt = pix_chan2_rsci_ogwt & pix_chan2_rsci_ivld;
  assign pix_chan2_rsci_ogwt = pix_chan2_rsci_oswt & (~ pix_chan2_rsci_bcwt);
  assign pix_chan2_rsci_irdy_run_sct = pix_chan2_rsci_ogwt;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_dy_chan_rsci_dy_chan_wait_dp
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_dy_chan_rsci_dy_chan_wait_dp (
  clk, rst, arst_n, dy_chan_rsci_oswt, dy_chan_rsci_wen_comp, dy_chan_rsci_idat_mxwt,
      dy_chan_rsci_biwt, dy_chan_rsci_bdwt, dy_chan_rsci_bcwt, dy_chan_rsci_idat
);
  input clk;
  input rst;
  input arst_n;
  input dy_chan_rsci_oswt;
  output dy_chan_rsci_wen_comp;
  output [35:0] dy_chan_rsci_idat_mxwt;
  input dy_chan_rsci_biwt;
  input dy_chan_rsci_bdwt;
  output dy_chan_rsci_bcwt;
  reg dy_chan_rsci_bcwt;
  input [35:0] dy_chan_rsci_idat;


  // Interconnect Declarations
  reg [35:0] dy_chan_rsci_idat_bfwt;


  // Interconnect Declarations for Component Instantiations 
  assign dy_chan_rsci_wen_comp = (~ dy_chan_rsci_oswt) | dy_chan_rsci_biwt | dy_chan_rsci_bcwt;
  assign dy_chan_rsci_idat_mxwt = MUX_v_36_2_2(dy_chan_rsci_idat, dy_chan_rsci_idat_bfwt,
      dy_chan_rsci_bcwt);
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      dy_chan_rsci_bcwt <= 1'b0;
    end
    else if ( rst ) begin
      dy_chan_rsci_bcwt <= 1'b0;
    end
    else begin
      dy_chan_rsci_bcwt <= ~((~(dy_chan_rsci_bcwt | dy_chan_rsci_biwt)) | dy_chan_rsci_bdwt);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      dy_chan_rsci_idat_bfwt <= 36'b000000000000000000000000000000000000;
    end
    else if ( rst ) begin
      dy_chan_rsci_idat_bfwt <= 36'b000000000000000000000000000000000000;
    end
    else if ( dy_chan_rsci_biwt ) begin
      dy_chan_rsci_idat_bfwt <= dy_chan_rsci_idat;
    end
  end

  function automatic [35:0] MUX_v_36_2_2;
    input [35:0] input_0;
    input [35:0] input_1;
    input  sel;
    reg [35:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_36_2_2 = result;
  end
  endfunction

endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_dy_chan_rsci_dy_chan_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_dy_chan_rsci_dy_chan_wait_ctrl (
  run_wen, dy_chan_rsci_oswt, dy_chan_rsci_biwt, dy_chan_rsci_bdwt, dy_chan_rsci_bcwt,
      dy_chan_rsci_irdy_run_sct, dy_chan_rsci_ivld
);
  input run_wen;
  input dy_chan_rsci_oswt;
  output dy_chan_rsci_biwt;
  output dy_chan_rsci_bdwt;
  input dy_chan_rsci_bcwt;
  output dy_chan_rsci_irdy_run_sct;
  input dy_chan_rsci_ivld;


  // Interconnect Declarations
  wire dy_chan_rsci_ogwt;


  // Interconnect Declarations for Component Instantiations 
  assign dy_chan_rsci_bdwt = dy_chan_rsci_oswt & run_wen;
  assign dy_chan_rsci_biwt = dy_chan_rsci_ogwt & dy_chan_rsci_ivld;
  assign dy_chan_rsci_ogwt = dy_chan_rsci_oswt & (~ dy_chan_rsci_bcwt);
  assign dy_chan_rsci_irdy_run_sct = dy_chan_rsci_ogwt;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_dx_chan_rsci_dx_chan_wait_dp
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_dx_chan_rsci_dx_chan_wait_dp (
  clk, rst, arst_n, dx_chan_rsci_oswt, dx_chan_rsci_wen_comp, dx_chan_rsci_idat_mxwt,
      dx_chan_rsci_biwt, dx_chan_rsci_bdwt, dx_chan_rsci_bcwt, dx_chan_rsci_idat
);
  input clk;
  input rst;
  input arst_n;
  input dx_chan_rsci_oswt;
  output dx_chan_rsci_wen_comp;
  output [35:0] dx_chan_rsci_idat_mxwt;
  input dx_chan_rsci_biwt;
  input dx_chan_rsci_bdwt;
  output dx_chan_rsci_bcwt;
  reg dx_chan_rsci_bcwt;
  input [35:0] dx_chan_rsci_idat;


  // Interconnect Declarations
  reg [35:0] dx_chan_rsci_idat_bfwt;


  // Interconnect Declarations for Component Instantiations 
  assign dx_chan_rsci_wen_comp = (~ dx_chan_rsci_oswt) | dx_chan_rsci_biwt | dx_chan_rsci_bcwt;
  assign dx_chan_rsci_idat_mxwt = MUX_v_36_2_2(dx_chan_rsci_idat, dx_chan_rsci_idat_bfwt,
      dx_chan_rsci_bcwt);
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      dx_chan_rsci_bcwt <= 1'b0;
    end
    else if ( rst ) begin
      dx_chan_rsci_bcwt <= 1'b0;
    end
    else begin
      dx_chan_rsci_bcwt <= ~((~(dx_chan_rsci_bcwt | dx_chan_rsci_biwt)) | dx_chan_rsci_bdwt);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      dx_chan_rsci_idat_bfwt <= 36'b000000000000000000000000000000000000;
    end
    else if ( rst ) begin
      dx_chan_rsci_idat_bfwt <= 36'b000000000000000000000000000000000000;
    end
    else if ( dx_chan_rsci_biwt ) begin
      dx_chan_rsci_idat_bfwt <= dx_chan_rsci_idat;
    end
  end

  function automatic [35:0] MUX_v_36_2_2;
    input [35:0] input_0;
    input [35:0] input_1;
    input  sel;
    reg [35:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_36_2_2 = result;
  end
  endfunction

endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_dx_chan_rsci_dx_chan_wait_ctrl
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_dx_chan_rsci_dx_chan_wait_ctrl (
  run_wen, dx_chan_rsci_oswt, dx_chan_rsci_biwt, dx_chan_rsci_bdwt, dx_chan_rsci_bcwt,
      dx_chan_rsci_irdy_run_sct, dx_chan_rsci_ivld
);
  input run_wen;
  input dx_chan_rsci_oswt;
  output dx_chan_rsci_biwt;
  output dx_chan_rsci_bdwt;
  input dx_chan_rsci_bcwt;
  output dx_chan_rsci_irdy_run_sct;
  input dx_chan_rsci_ivld;


  // Interconnect Declarations
  wire dx_chan_rsci_ogwt;


  // Interconnect Declarations for Component Instantiations 
  assign dx_chan_rsci_bdwt = dx_chan_rsci_oswt & run_wen;
  assign dx_chan_rsci_biwt = dx_chan_rsci_ogwt & dx_chan_rsci_ivld;
  assign dx_chan_rsci_ogwt = dx_chan_rsci_oswt & (~ dx_chan_rsci_bcwt);
  assign dx_chan_rsci_irdy_run_sct = dx_chan_rsci_ogwt;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf1_rsci_1
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf1_rsci_1 (
  clk, rst, arst_n, line_buf1_rsci_q_d, run_wen, run_wten, line_buf1_rsci_oswt_unreg,
      line_buf1_rsci_bawt, line_buf1_rsci_iswt0, line_buf1_rsci_q_d_mxwt, line_buf1_rsci_re_d_pff,
      line_buf1_rsci_iswt0_pff, line_buf1_rsci_we_d_pff, line_buf1_rsci_iswt0_1_pff
);
  input clk;
  input rst;
  input arst_n;
  input [63:0] line_buf1_rsci_q_d;
  input run_wen;
  input run_wten;
  input line_buf1_rsci_oswt_unreg;
  output line_buf1_rsci_bawt;
  input line_buf1_rsci_iswt0;
  output [63:0] line_buf1_rsci_q_d_mxwt;
  output line_buf1_rsci_re_d_pff;
  input line_buf1_rsci_iswt0_pff;
  output line_buf1_rsci_we_d_pff;
  input line_buf1_rsci_iswt0_1_pff;


  // Interconnect Declarations
  wire line_buf1_rsci_biwt;
  wire line_buf1_rsci_bdwt;
  wire line_buf1_rsci_re_d_run_sct_iff;
  wire line_buf1_rsci_we_d_run_sct_iff;


  // Interconnect Declarations for Component Instantiations 
  EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf1_rsci_1_line_buf1_rsc_wait_ctrl EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf1_rsci_1_line_buf1_rsc_wait_ctrl_inst
      (
      .run_wen(run_wen),
      .run_wten(run_wten),
      .line_buf1_rsci_oswt_unreg(line_buf1_rsci_oswt_unreg),
      .line_buf1_rsci_iswt0(line_buf1_rsci_iswt0),
      .line_buf1_rsci_biwt(line_buf1_rsci_biwt),
      .line_buf1_rsci_bdwt(line_buf1_rsci_bdwt),
      .line_buf1_rsci_re_d_run_sct_pff(line_buf1_rsci_re_d_run_sct_iff),
      .line_buf1_rsci_iswt0_pff(line_buf1_rsci_iswt0_pff),
      .line_buf1_rsci_we_d_run_sct_pff(line_buf1_rsci_we_d_run_sct_iff),
      .line_buf1_rsci_iswt0_1_pff(line_buf1_rsci_iswt0_1_pff)
    );
  EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf1_rsci_1_line_buf1_rsc_wait_dp EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf1_rsci_1_line_buf1_rsc_wait_dp_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .line_buf1_rsci_q_d(line_buf1_rsci_q_d),
      .line_buf1_rsci_bawt(line_buf1_rsci_bawt),
      .line_buf1_rsci_q_d_mxwt(line_buf1_rsci_q_d_mxwt),
      .line_buf1_rsci_biwt(line_buf1_rsci_biwt),
      .line_buf1_rsci_bdwt(line_buf1_rsci_bdwt)
    );
  assign line_buf1_rsci_re_d_pff = line_buf1_rsci_re_d_run_sct_iff;
  assign line_buf1_rsci_we_d_pff = line_buf1_rsci_we_d_run_sct_iff;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf0_rsci_1
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf0_rsci_1 (
  clk, rst, arst_n, line_buf0_rsci_q_d, run_wen, run_wten, line_buf0_rsci_oswt_unreg,
      line_buf0_rsci_bawt, line_buf0_rsci_iswt0, line_buf0_rsci_q_d_mxwt, line_buf0_rsci_re_d_pff,
      line_buf0_rsci_iswt0_pff, line_buf0_rsci_we_d_pff, line_buf0_rsci_iswt0_1_pff
);
  input clk;
  input rst;
  input arst_n;
  input [63:0] line_buf0_rsci_q_d;
  input run_wen;
  input run_wten;
  input line_buf0_rsci_oswt_unreg;
  output line_buf0_rsci_bawt;
  input line_buf0_rsci_iswt0;
  output [63:0] line_buf0_rsci_q_d_mxwt;
  output line_buf0_rsci_re_d_pff;
  input line_buf0_rsci_iswt0_pff;
  output line_buf0_rsci_we_d_pff;
  input line_buf0_rsci_iswt0_1_pff;


  // Interconnect Declarations
  wire line_buf0_rsci_biwt;
  wire line_buf0_rsci_bdwt;
  wire line_buf0_rsci_re_d_run_sct_iff;
  wire line_buf0_rsci_we_d_run_sct_iff;


  // Interconnect Declarations for Component Instantiations 
  EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf0_rsci_1_line_buf0_rsc_wait_ctrl EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf0_rsci_1_line_buf0_rsc_wait_ctrl_inst
      (
      .run_wen(run_wen),
      .run_wten(run_wten),
      .line_buf0_rsci_oswt_unreg(line_buf0_rsci_oswt_unreg),
      .line_buf0_rsci_iswt0(line_buf0_rsci_iswt0),
      .line_buf0_rsci_biwt(line_buf0_rsci_biwt),
      .line_buf0_rsci_bdwt(line_buf0_rsci_bdwt),
      .line_buf0_rsci_re_d_run_sct_pff(line_buf0_rsci_re_d_run_sct_iff),
      .line_buf0_rsci_iswt0_pff(line_buf0_rsci_iswt0_pff),
      .line_buf0_rsci_we_d_run_sct_pff(line_buf0_rsci_we_d_run_sct_iff),
      .line_buf0_rsci_iswt0_1_pff(line_buf0_rsci_iswt0_1_pff)
    );
  EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf0_rsci_1_line_buf0_rsc_wait_dp EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf0_rsci_1_line_buf0_rsc_wait_dp_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .line_buf0_rsci_q_d(line_buf0_rsci_q_d),
      .line_buf0_rsci_bawt(line_buf0_rsci_bawt),
      .line_buf0_rsci_q_d_mxwt(line_buf0_rsci_q_d_mxwt),
      .line_buf0_rsci_biwt(line_buf0_rsci_biwt),
      .line_buf0_rsci_bdwt(line_buf0_rsci_bdwt)
    );
  assign line_buf0_rsci_re_d_pff = line_buf0_rsci_re_d_run_sct_iff;
  assign line_buf0_rsci_we_d_pff = line_buf0_rsci_we_d_run_sct_iff;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_run_dy_chan_rsci
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_run_dy_chan_rsci (
  clk, rst, arst_n, dy_chan_rsc_dat, dy_chan_rsc_vld, dy_chan_rsc_rdy, run_wen, dy_chan_rsci_oswt_unreg,
      dy_chan_rsci_bawt, dy_chan_rsci_iswt0, dy_chan_rsci_wen_comp, dy_chan_rsci_idat
);
  input clk;
  input rst;
  input arst_n;
  output [35:0] dy_chan_rsc_dat;
  output dy_chan_rsc_vld;
  input dy_chan_rsc_rdy;
  input run_wen;
  input dy_chan_rsci_oswt_unreg;
  output dy_chan_rsci_bawt;
  input dy_chan_rsci_iswt0;
  output dy_chan_rsci_wen_comp;
  input [35:0] dy_chan_rsci_idat;


  // Interconnect Declarations
  wire dy_chan_rsci_biwt;
  wire dy_chan_rsci_bdwt;
  wire dy_chan_rsci_bcwt;
  wire dy_chan_rsci_irdy;
  wire dy_chan_rsci_ivld_run_sct;


  // Interconnect Declarations for Component Instantiations 
  ccs_out_wait_v1 #(.rscid(32'sd5),
  .width(32'sd36)) dy_chan_rsci (
      .irdy(dy_chan_rsci_irdy),
      .ivld(dy_chan_rsci_ivld_run_sct),
      .idat(dy_chan_rsci_idat),
      .rdy(dy_chan_rsc_rdy),
      .vld(dy_chan_rsc_vld),
      .dat(dy_chan_rsc_dat)
    );
  EdgeDetect_IP_EdgeDetect_VerDer_run_dy_chan_rsci_dy_chan_wait_ctrl EdgeDetect_IP_EdgeDetect_VerDer_run_dy_chan_rsci_dy_chan_wait_ctrl_inst
      (
      .run_wen(run_wen),
      .dy_chan_rsci_oswt_unreg(dy_chan_rsci_oswt_unreg),
      .dy_chan_rsci_iswt0(dy_chan_rsci_iswt0),
      .dy_chan_rsci_biwt(dy_chan_rsci_biwt),
      .dy_chan_rsci_bdwt(dy_chan_rsci_bdwt),
      .dy_chan_rsci_bcwt(dy_chan_rsci_bcwt),
      .dy_chan_rsci_irdy(dy_chan_rsci_irdy),
      .dy_chan_rsci_ivld_run_sct(dy_chan_rsci_ivld_run_sct)
    );
  EdgeDetect_IP_EdgeDetect_VerDer_run_dy_chan_rsci_dy_chan_wait_dp EdgeDetect_IP_EdgeDetect_VerDer_run_dy_chan_rsci_dy_chan_wait_dp_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dy_chan_rsci_oswt_unreg(dy_chan_rsci_oswt_unreg),
      .dy_chan_rsci_bawt(dy_chan_rsci_bawt),
      .dy_chan_rsci_wen_comp(dy_chan_rsci_wen_comp),
      .dy_chan_rsci_biwt(dy_chan_rsci_biwt),
      .dy_chan_rsci_bdwt(dy_chan_rsci_bdwt),
      .dy_chan_rsci_bcwt(dy_chan_rsci_bcwt)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_run_pix_chan1_rsci
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_run_pix_chan1_rsci (
  clk, rst, arst_n, pix_chan1_rsc_dat, pix_chan1_rsc_vld, pix_chan1_rsc_rdy, run_wen,
      pix_chan1_rsci_oswt_unreg, pix_chan1_rsci_bawt, pix_chan1_rsci_iswt0, pix_chan1_rsci_wen_comp,
      pix_chan1_rsci_idat
);
  input clk;
  input rst;
  input arst_n;
  output [31:0] pix_chan1_rsc_dat;
  output pix_chan1_rsc_vld;
  input pix_chan1_rsc_rdy;
  input run_wen;
  input pix_chan1_rsci_oswt_unreg;
  output pix_chan1_rsci_bawt;
  input pix_chan1_rsci_iswt0;
  output pix_chan1_rsci_wen_comp;
  input [31:0] pix_chan1_rsci_idat;


  // Interconnect Declarations
  wire pix_chan1_rsci_biwt;
  wire pix_chan1_rsci_bdwt;
  wire pix_chan1_rsci_bcwt;
  wire pix_chan1_rsci_irdy;
  wire pix_chan1_rsci_ivld_run_sct;


  // Interconnect Declarations for Component Instantiations 
  ccs_out_wait_v1 #(.rscid(32'sd4),
  .width(32'sd32)) pix_chan1_rsci (
      .irdy(pix_chan1_rsci_irdy),
      .ivld(pix_chan1_rsci_ivld_run_sct),
      .idat(pix_chan1_rsci_idat),
      .rdy(pix_chan1_rsc_rdy),
      .vld(pix_chan1_rsc_vld),
      .dat(pix_chan1_rsc_dat)
    );
  EdgeDetect_IP_EdgeDetect_VerDer_run_pix_chan1_rsci_pix_chan1_wait_ctrl EdgeDetect_IP_EdgeDetect_VerDer_run_pix_chan1_rsci_pix_chan1_wait_ctrl_inst
      (
      .run_wen(run_wen),
      .pix_chan1_rsci_oswt_unreg(pix_chan1_rsci_oswt_unreg),
      .pix_chan1_rsci_iswt0(pix_chan1_rsci_iswt0),
      .pix_chan1_rsci_biwt(pix_chan1_rsci_biwt),
      .pix_chan1_rsci_bdwt(pix_chan1_rsci_bdwt),
      .pix_chan1_rsci_bcwt(pix_chan1_rsci_bcwt),
      .pix_chan1_rsci_irdy(pix_chan1_rsci_irdy),
      .pix_chan1_rsci_ivld_run_sct(pix_chan1_rsci_ivld_run_sct)
    );
  EdgeDetect_IP_EdgeDetect_VerDer_run_pix_chan1_rsci_pix_chan1_wait_dp EdgeDetect_IP_EdgeDetect_VerDer_run_pix_chan1_rsci_pix_chan1_wait_dp_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .pix_chan1_rsci_oswt_unreg(pix_chan1_rsci_oswt_unreg),
      .pix_chan1_rsci_bawt(pix_chan1_rsci_bawt),
      .pix_chan1_rsci_wen_comp(pix_chan1_rsci_wen_comp),
      .pix_chan1_rsci_biwt(pix_chan1_rsci_biwt),
      .pix_chan1_rsci_bdwt(pix_chan1_rsci_bdwt),
      .pix_chan1_rsci_bcwt(pix_chan1_rsci_bcwt)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_run_dat_in_rsci
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_run_dat_in_rsci (
  dat_in_rsc_dat, dat_in_rsc_vld, dat_in_rsc_rdy, run_wen, dat_in_rsci_oswt_unreg,
      dat_in_rsci_biwt, dat_in_rsci_iswt0, dat_in_rsci_wen_comp, dat_in_rsci_idat_mxwt
);
  input [33:0] dat_in_rsc_dat;
  input dat_in_rsc_vld;
  output dat_in_rsc_rdy;
  input run_wen;
  input dat_in_rsci_oswt_unreg;
  output dat_in_rsci_biwt;
  input dat_in_rsci_iswt0;
  output dat_in_rsci_wen_comp;
  output [31:0] dat_in_rsci_idat_mxwt;


  // Interconnect Declarations
  wire dat_in_rsci_irdy_run_sct;
  wire dat_in_rsci_ivld;
  wire [33:0] dat_in_rsci_idat;


  // Interconnect Declarations for Component Instantiations 
  ccs_in_wait_coupled_v1 #(.rscid(32'sd1),
  .width(32'sd34)) dat_in_rsci (
      .rdy(dat_in_rsc_rdy),
      .vld(dat_in_rsc_vld),
      .dat(dat_in_rsc_dat),
      .irdy(dat_in_rsci_irdy_run_sct),
      .ivld(dat_in_rsci_ivld),
      .idat(dat_in_rsci_idat)
    );
  EdgeDetect_IP_EdgeDetect_VerDer_run_dat_in_rsci_dat_in_wait_ctrl EdgeDetect_IP_EdgeDetect_VerDer_run_dat_in_rsci_dat_in_wait_ctrl_inst
      (
      .run_wen(run_wen),
      .dat_in_rsci_oswt_unreg(dat_in_rsci_oswt_unreg),
      .dat_in_rsci_iswt0(dat_in_rsci_iswt0),
      .dat_in_rsci_irdy_run_sct(dat_in_rsci_irdy_run_sct)
    );
  assign dat_in_rsci_idat_mxwt = dat_in_rsci_idat[31:0];
  assign dat_in_rsci_biwt = dat_in_rsci_ivld;
  assign dat_in_rsci_wen_comp = (~ dat_in_rsci_oswt_unreg) | dat_in_rsci_biwt;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_HorDer_run_dx_chan_rsci
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_HorDer_run_dx_chan_rsci (
  dx_chan_rsc_dat, dx_chan_rsc_vld, dx_chan_rsc_rdy, dx_chan_rsci_oswt, dx_chan_rsci_wen_comp,
      dx_chan_rsci_idat
);
  output [35:0] dx_chan_rsc_dat;
  output dx_chan_rsc_vld;
  input dx_chan_rsc_rdy;
  input dx_chan_rsci_oswt;
  output dx_chan_rsci_wen_comp;
  input [35:0] dx_chan_rsci_idat;


  // Interconnect Declarations
  wire dx_chan_rsci_biwt;
  wire dx_chan_rsci_irdy;


  // Interconnect Declarations for Component Instantiations 
  ccs_out_wait_v1 #(.rscid(32'sd12),
  .width(32'sd36)) dx_chan_rsci (
      .irdy(dx_chan_rsci_irdy),
      .ivld(dx_chan_rsci_oswt),
      .idat(dx_chan_rsci_idat),
      .rdy(dx_chan_rsc_rdy),
      .vld(dx_chan_rsc_vld),
      .dat(dx_chan_rsc_dat)
    );
  EdgeDetect_IP_EdgeDetect_HorDer_run_dx_chan_rsci_dx_chan_wait_ctrl EdgeDetect_IP_EdgeDetect_HorDer_run_dx_chan_rsci_dx_chan_wait_ctrl_inst
      (
      .dx_chan_rsci_iswt0(dx_chan_rsci_oswt),
      .dx_chan_rsci_biwt(dx_chan_rsci_biwt),
      .dx_chan_rsci_irdy(dx_chan_rsci_irdy)
    );
  assign dx_chan_rsci_wen_comp = (~ dx_chan_rsci_oswt) | dx_chan_rsci_biwt;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_HorDer_run_pix_chan2_rsci
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_HorDer_run_pix_chan2_rsci (
  pix_chan2_rsc_dat, pix_chan2_rsc_vld, pix_chan2_rsc_rdy, pix_chan2_rsci_oswt, pix_chan2_rsci_wen_comp,
      pix_chan2_rsci_idat
);
  output [31:0] pix_chan2_rsc_dat;
  output pix_chan2_rsc_vld;
  input pix_chan2_rsc_rdy;
  input pix_chan2_rsci_oswt;
  output pix_chan2_rsci_wen_comp;
  input [31:0] pix_chan2_rsci_idat;


  // Interconnect Declarations
  wire pix_chan2_rsci_biwt;
  wire pix_chan2_rsci_irdy;


  // Interconnect Declarations for Component Instantiations 
  ccs_out_wait_v1 #(.rscid(32'sd11),
  .width(32'sd32)) pix_chan2_rsci (
      .irdy(pix_chan2_rsci_irdy),
      .ivld(pix_chan2_rsci_oswt),
      .idat(pix_chan2_rsci_idat),
      .rdy(pix_chan2_rsc_rdy),
      .vld(pix_chan2_rsc_vld),
      .dat(pix_chan2_rsc_dat)
    );
  EdgeDetect_IP_EdgeDetect_HorDer_run_pix_chan2_rsci_pix_chan2_wait_ctrl EdgeDetect_IP_EdgeDetect_HorDer_run_pix_chan2_rsci_pix_chan2_wait_ctrl_inst
      (
      .pix_chan2_rsci_iswt0(pix_chan2_rsci_oswt),
      .pix_chan2_rsci_biwt(pix_chan2_rsci_biwt),
      .pix_chan2_rsci_irdy(pix_chan2_rsci_irdy)
    );
  assign pix_chan2_rsci_wen_comp = (~ pix_chan2_rsci_oswt) | pix_chan2_rsci_biwt;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_HorDer_run_pix_chan1_rsci
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_HorDer_run_pix_chan1_rsci (
  pix_chan1_rsc_dat, pix_chan1_rsc_vld, pix_chan1_rsc_rdy, pix_chan1_rsci_oswt, pix_chan1_rsci_wen_comp,
      pix_chan1_rsci_idat_mxwt
);
  input [31:0] pix_chan1_rsc_dat;
  input pix_chan1_rsc_vld;
  output pix_chan1_rsc_rdy;
  input pix_chan1_rsci_oswt;
  output pix_chan1_rsci_wen_comp;
  output [31:0] pix_chan1_rsci_idat_mxwt;


  // Interconnect Declarations
  wire pix_chan1_rsci_biwt;
  wire pix_chan1_rsci_ivld;
  wire [31:0] pix_chan1_rsci_idat;


  // Interconnect Declarations for Component Instantiations 
  ccs_in_wait_v1 #(.rscid(32'sd8),
  .width(32'sd32)) pix_chan1_rsci (
      .rdy(pix_chan1_rsc_rdy),
      .vld(pix_chan1_rsc_vld),
      .dat(pix_chan1_rsc_dat),
      .irdy(pix_chan1_rsci_oswt),
      .ivld(pix_chan1_rsci_ivld),
      .idat(pix_chan1_rsci_idat)
    );
  EdgeDetect_IP_EdgeDetect_HorDer_run_pix_chan1_rsci_pix_chan1_wait_ctrl EdgeDetect_IP_EdgeDetect_HorDer_run_pix_chan1_rsci_pix_chan1_wait_ctrl_inst
      (
      .pix_chan1_rsci_iswt0(pix_chan1_rsci_oswt),
      .pix_chan1_rsci_biwt(pix_chan1_rsci_biwt),
      .pix_chan1_rsci_ivld(pix_chan1_rsci_ivld)
    );
  assign pix_chan1_rsci_idat_mxwt = pix_chan1_rsci_idat;
  assign pix_chan1_rsci_wen_comp = (~ pix_chan1_rsci_oswt) | pix_chan1_rsci_biwt;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_triosy_obj
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_triosy_obj (
  crc32_dat_out_triosy_lz, run_wten, crc32_dat_out_triosy_obj_iswt0
);
  output crc32_dat_out_triosy_lz;
  input run_wten;
  input crc32_dat_out_triosy_obj_iswt0;


  // Interconnect Declarations
  wire crc32_dat_out_triosy_obj_biwt;


  // Interconnect Declarations for Component Instantiations 
  mgc_io_sync_v2 #(.valid(32'sd0)) crc32_dat_out_triosy_obj (
      .ld(crc32_dat_out_triosy_obj_biwt),
      .lz(crc32_dat_out_triosy_lz)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_triosy_obj_crc32_dat_out_triosy_wait_ctrl
      EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_triosy_obj_crc32_dat_out_triosy_wait_ctrl_inst
      (
      .run_wten(run_wten),
      .crc32_dat_out_triosy_obj_iswt0(crc32_dat_out_triosy_obj_iswt0),
      .crc32_dat_out_triosy_obj_biwt(crc32_dat_out_triosy_obj_biwt)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_triosy_obj
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_triosy_obj (
  crc32_pix_in_triosy_lz, run_wten, crc32_pix_in_triosy_obj_iswt0
);
  output crc32_pix_in_triosy_lz;
  input run_wten;
  input crc32_pix_in_triosy_obj_iswt0;


  // Interconnect Declarations
  wire crc32_pix_in_triosy_obj_biwt;


  // Interconnect Declarations for Component Instantiations 
  mgc_io_sync_v2 #(.valid(32'sd0)) crc32_pix_in_triosy_obj (
      .ld(crc32_pix_in_triosy_obj_biwt),
      .lz(crc32_pix_in_triosy_lz)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_triosy_obj_crc32_pix_in_triosy_wait_ctrl
      EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_triosy_obj_crc32_pix_in_triosy_wait_ctrl_inst
      (
      .run_wten(run_wten),
      .crc32_pix_in_triosy_obj_iswt0(crc32_pix_in_triosy_obj_iswt0),
      .crc32_pix_in_triosy_obj_biwt(crc32_pix_in_triosy_obj_biwt)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_sw_in_triosy_obj
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_sw_in_triosy_obj (
  sw_in_triosy_lz, run_wten, sw_in_triosy_obj_iswt0
);
  output sw_in_triosy_lz;
  input run_wten;
  input sw_in_triosy_obj_iswt0;


  // Interconnect Declarations
  wire sw_in_triosy_obj_biwt;


  // Interconnect Declarations for Component Instantiations 
  mgc_io_sync_v2 #(.valid(32'sd0)) sw_in_triosy_obj (
      .ld(sw_in_triosy_obj_biwt),
      .lz(sw_in_triosy_lz)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_sw_in_triosy_obj_sw_in_triosy_wait_ctrl EdgeDetect_IP_EdgeDetect_MagAng_run_sw_in_triosy_obj_sw_in_triosy_wait_ctrl_inst
      (
      .run_wten(run_wten),
      .sw_in_triosy_obj_iswt0(sw_in_triosy_obj_iswt0),
      .sw_in_triosy_obj_biwt(sw_in_triosy_obj_biwt)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_dat_out_rsci
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_dat_out_rsci (
  dat_out_rsc_dat, dat_out_rsc_vld, dat_out_rsc_rdy, dat_out_rsci_oswt, dat_out_rsci_wen_comp,
      dat_out_rsci_idat
);
  output [33:0] dat_out_rsc_dat;
  output dat_out_rsc_vld;
  input dat_out_rsc_rdy;
  input dat_out_rsci_oswt;
  output dat_out_rsci_wen_comp;
  input [33:0] dat_out_rsci_idat;


  // Interconnect Declarations
  wire dat_out_rsci_biwt;
  wire dat_out_rsci_irdy;


  // Interconnect Declarations for Component Instantiations 
  ccs_out_wait_v1 #(.rscid(32'sd21),
  .width(32'sd34)) dat_out_rsci (
      .irdy(dat_out_rsci_irdy),
      .ivld(dat_out_rsci_oswt),
      .idat(dat_out_rsci_idat),
      .rdy(dat_out_rsc_rdy),
      .vld(dat_out_rsc_vld),
      .dat(dat_out_rsc_dat)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_dat_out_rsci_dat_out_wait_ctrl EdgeDetect_IP_EdgeDetect_MagAng_run_dat_out_rsci_dat_out_wait_ctrl_inst
      (
      .dat_out_rsci_iswt0(dat_out_rsci_oswt),
      .dat_out_rsci_biwt(dat_out_rsci_biwt),
      .dat_out_rsci_irdy(dat_out_rsci_irdy)
    );
  assign dat_out_rsci_wen_comp = (~ dat_out_rsci_oswt) | dat_out_rsci_biwt;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_rsci
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_rsci (
  crc32_dat_out_rsc_zout, crc32_dat_out_rsc_lzout, crc32_dat_out_rsc_zin, run_wten,
      crc32_dat_out_rsci_iswt0, crc32_dat_out_rsci_din, crc32_dat_out_rsci_dout_run
);
  output [31:0] crc32_dat_out_rsc_zout;
  output crc32_dat_out_rsc_lzout;
  input [31:0] crc32_dat_out_rsc_zin;
  input run_wten;
  input crc32_dat_out_rsci_iswt0;
  output [31:0] crc32_dat_out_rsci_din;
  input [31:0] crc32_dat_out_rsci_dout_run;


  // Interconnect Declarations
  wire crc32_dat_out_rsci_ldout_run_sct;


  // Interconnect Declarations for Component Instantiations 
  mgc_inout_prereg_en_v1 #(.rscid(32'sd20),
  .width(32'sd32)) crc32_dat_out_rsci (
      .din(crc32_dat_out_rsci_din),
      .ldout(crc32_dat_out_rsci_ldout_run_sct),
      .dout(crc32_dat_out_rsci_dout_run),
      .zin(crc32_dat_out_rsc_zin),
      .lzout(crc32_dat_out_rsc_lzout),
      .zout(crc32_dat_out_rsc_zout)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_rsci_crc32_dat_out_rsc_wait_ctrl
      EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_rsci_crc32_dat_out_rsc_wait_ctrl_inst
      (
      .run_wten(run_wten),
      .crc32_dat_out_rsci_iswt0(crc32_dat_out_rsci_iswt0),
      .crc32_dat_out_rsci_ldout_run_sct(crc32_dat_out_rsci_ldout_run_sct)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_rsci
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_rsci (
  crc32_pix_in_rsc_zout, crc32_pix_in_rsc_lzout, crc32_pix_in_rsc_zin, run_wten,
      crc32_pix_in_rsci_iswt0, crc32_pix_in_rsci_din, crc32_pix_in_rsci_dout_run
);
  output [31:0] crc32_pix_in_rsc_zout;
  output crc32_pix_in_rsc_lzout;
  input [31:0] crc32_pix_in_rsc_zin;
  input run_wten;
  input crc32_pix_in_rsci_iswt0;
  output [31:0] crc32_pix_in_rsci_din;
  input [31:0] crc32_pix_in_rsci_dout_run;


  // Interconnect Declarations
  wire crc32_pix_in_rsci_ldout_run_sct;


  // Interconnect Declarations for Component Instantiations 
  mgc_inout_prereg_en_v1 #(.rscid(32'sd19),
  .width(32'sd32)) crc32_pix_in_rsci (
      .din(crc32_pix_in_rsci_din),
      .ldout(crc32_pix_in_rsci_ldout_run_sct),
      .dout(crc32_pix_in_rsci_dout_run),
      .zin(crc32_pix_in_rsc_zin),
      .lzout(crc32_pix_in_rsc_lzout),
      .zout(crc32_pix_in_rsc_zout)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_rsci_crc32_pix_in_rsc_wait_ctrl
      EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_rsci_crc32_pix_in_rsc_wait_ctrl_inst
      (
      .run_wten(run_wten),
      .crc32_pix_in_rsci_iswt0(crc32_pix_in_rsci_iswt0),
      .crc32_pix_in_rsci_ldout_run_sct(crc32_pix_in_rsci_ldout_run_sct)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_pix_chan2_rsci
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_pix_chan2_rsci (
  clk, rst, arst_n, pix_chan2_rsc_dat, pix_chan2_rsc_vld, pix_chan2_rsc_rdy, run_wen,
      pix_chan2_rsci_oswt, pix_chan2_rsci_wen_comp, pix_chan2_rsci_idat_mxwt
);
  input clk;
  input rst;
  input arst_n;
  input [31:0] pix_chan2_rsc_dat;
  input pix_chan2_rsc_vld;
  output pix_chan2_rsc_rdy;
  input run_wen;
  input pix_chan2_rsci_oswt;
  output pix_chan2_rsci_wen_comp;
  output [31:0] pix_chan2_rsci_idat_mxwt;


  // Interconnect Declarations
  wire pix_chan2_rsci_biwt;
  wire pix_chan2_rsci_bdwt;
  wire pix_chan2_rsci_bcwt;
  wire pix_chan2_rsci_irdy_run_sct;
  wire pix_chan2_rsci_ivld;
  wire [31:0] pix_chan2_rsci_idat;


  // Interconnect Declarations for Component Instantiations 
  ccs_in_wait_v1 #(.rscid(32'sd15),
  .width(32'sd32)) pix_chan2_rsci (
      .rdy(pix_chan2_rsc_rdy),
      .vld(pix_chan2_rsc_vld),
      .dat(pix_chan2_rsc_dat),
      .irdy(pix_chan2_rsci_irdy_run_sct),
      .ivld(pix_chan2_rsci_ivld),
      .idat(pix_chan2_rsci_idat)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_pix_chan2_rsci_pix_chan2_wait_ctrl EdgeDetect_IP_EdgeDetect_MagAng_run_pix_chan2_rsci_pix_chan2_wait_ctrl_inst
      (
      .run_wen(run_wen),
      .pix_chan2_rsci_oswt(pix_chan2_rsci_oswt),
      .pix_chan2_rsci_biwt(pix_chan2_rsci_biwt),
      .pix_chan2_rsci_bdwt(pix_chan2_rsci_bdwt),
      .pix_chan2_rsci_bcwt(pix_chan2_rsci_bcwt),
      .pix_chan2_rsci_irdy_run_sct(pix_chan2_rsci_irdy_run_sct),
      .pix_chan2_rsci_ivld(pix_chan2_rsci_ivld)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_pix_chan2_rsci_pix_chan2_wait_dp EdgeDetect_IP_EdgeDetect_MagAng_run_pix_chan2_rsci_pix_chan2_wait_dp_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .pix_chan2_rsci_oswt(pix_chan2_rsci_oswt),
      .pix_chan2_rsci_wen_comp(pix_chan2_rsci_wen_comp),
      .pix_chan2_rsci_idat_mxwt(pix_chan2_rsci_idat_mxwt),
      .pix_chan2_rsci_biwt(pix_chan2_rsci_biwt),
      .pix_chan2_rsci_bdwt(pix_chan2_rsci_bdwt),
      .pix_chan2_rsci_bcwt(pix_chan2_rsci_bcwt),
      .pix_chan2_rsci_idat(pix_chan2_rsci_idat)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_dy_chan_rsci
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_dy_chan_rsci (
  clk, rst, arst_n, dy_chan_rsc_dat, dy_chan_rsc_vld, dy_chan_rsc_rdy, run_wen, dy_chan_rsci_oswt,
      dy_chan_rsci_wen_comp, dy_chan_rsci_idat_mxwt
);
  input clk;
  input rst;
  input arst_n;
  input [35:0] dy_chan_rsc_dat;
  input dy_chan_rsc_vld;
  output dy_chan_rsc_rdy;
  input run_wen;
  input dy_chan_rsci_oswt;
  output dy_chan_rsci_wen_comp;
  output [35:0] dy_chan_rsci_idat_mxwt;


  // Interconnect Declarations
  wire dy_chan_rsci_biwt;
  wire dy_chan_rsci_bdwt;
  wire dy_chan_rsci_bcwt;
  wire dy_chan_rsci_irdy_run_sct;
  wire dy_chan_rsci_ivld;
  wire [35:0] dy_chan_rsci_idat;


  // Interconnect Declarations for Component Instantiations 
  ccs_in_wait_v1 #(.rscid(32'sd14),
  .width(32'sd36)) dy_chan_rsci (
      .rdy(dy_chan_rsc_rdy),
      .vld(dy_chan_rsc_vld),
      .dat(dy_chan_rsc_dat),
      .irdy(dy_chan_rsci_irdy_run_sct),
      .ivld(dy_chan_rsci_ivld),
      .idat(dy_chan_rsci_idat)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_dy_chan_rsci_dy_chan_wait_ctrl EdgeDetect_IP_EdgeDetect_MagAng_run_dy_chan_rsci_dy_chan_wait_ctrl_inst
      (
      .run_wen(run_wen),
      .dy_chan_rsci_oswt(dy_chan_rsci_oswt),
      .dy_chan_rsci_biwt(dy_chan_rsci_biwt),
      .dy_chan_rsci_bdwt(dy_chan_rsci_bdwt),
      .dy_chan_rsci_bcwt(dy_chan_rsci_bcwt),
      .dy_chan_rsci_irdy_run_sct(dy_chan_rsci_irdy_run_sct),
      .dy_chan_rsci_ivld(dy_chan_rsci_ivld)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_dy_chan_rsci_dy_chan_wait_dp EdgeDetect_IP_EdgeDetect_MagAng_run_dy_chan_rsci_dy_chan_wait_dp_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dy_chan_rsci_oswt(dy_chan_rsci_oswt),
      .dy_chan_rsci_wen_comp(dy_chan_rsci_wen_comp),
      .dy_chan_rsci_idat_mxwt(dy_chan_rsci_idat_mxwt),
      .dy_chan_rsci_biwt(dy_chan_rsci_biwt),
      .dy_chan_rsci_bdwt(dy_chan_rsci_bdwt),
      .dy_chan_rsci_bcwt(dy_chan_rsci_bcwt),
      .dy_chan_rsci_idat(dy_chan_rsci_idat)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run_dx_chan_rsci
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run_dx_chan_rsci (
  clk, rst, arst_n, dx_chan_rsc_dat, dx_chan_rsc_vld, dx_chan_rsc_rdy, run_wen, dx_chan_rsci_oswt,
      dx_chan_rsci_wen_comp, dx_chan_rsci_idat_mxwt
);
  input clk;
  input rst;
  input arst_n;
  input [35:0] dx_chan_rsc_dat;
  input dx_chan_rsc_vld;
  output dx_chan_rsc_rdy;
  input run_wen;
  input dx_chan_rsci_oswt;
  output dx_chan_rsci_wen_comp;
  output [35:0] dx_chan_rsci_idat_mxwt;


  // Interconnect Declarations
  wire dx_chan_rsci_biwt;
  wire dx_chan_rsci_bdwt;
  wire dx_chan_rsci_bcwt;
  wire dx_chan_rsci_irdy_run_sct;
  wire dx_chan_rsci_ivld;
  wire [35:0] dx_chan_rsci_idat;


  // Interconnect Declarations for Component Instantiations 
  ccs_in_wait_v1 #(.rscid(32'sd13),
  .width(32'sd36)) dx_chan_rsci (
      .rdy(dx_chan_rsc_rdy),
      .vld(dx_chan_rsc_vld),
      .dat(dx_chan_rsc_dat),
      .irdy(dx_chan_rsci_irdy_run_sct),
      .ivld(dx_chan_rsci_ivld),
      .idat(dx_chan_rsci_idat)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_dx_chan_rsci_dx_chan_wait_ctrl EdgeDetect_IP_EdgeDetect_MagAng_run_dx_chan_rsci_dx_chan_wait_ctrl_inst
      (
      .run_wen(run_wen),
      .dx_chan_rsci_oswt(dx_chan_rsci_oswt),
      .dx_chan_rsci_biwt(dx_chan_rsci_biwt),
      .dx_chan_rsci_bdwt(dx_chan_rsci_bdwt),
      .dx_chan_rsci_bcwt(dx_chan_rsci_bcwt),
      .dx_chan_rsci_irdy_run_sct(dx_chan_rsci_irdy_run_sct),
      .dx_chan_rsci_ivld(dx_chan_rsci_ivld)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_dx_chan_rsci_dx_chan_wait_dp EdgeDetect_IP_EdgeDetect_MagAng_run_dx_chan_rsci_dx_chan_wait_dp_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dx_chan_rsci_oswt(dx_chan_rsci_oswt),
      .dx_chan_rsci_wen_comp(dx_chan_rsci_wen_comp),
      .dx_chan_rsci_idat_mxwt(dx_chan_rsci_idat_mxwt),
      .dx_chan_rsci_biwt(dx_chan_rsci_biwt),
      .dx_chan_rsci_bdwt(dx_chan_rsci_bdwt),
      .dx_chan_rsci_bcwt(dx_chan_rsci_bcwt),
      .dx_chan_rsci_idat(dx_chan_rsci_idat)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer_run
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer_run (
  clk, rst, arst_n, dat_in_rsc_dat, dat_in_rsc_vld, dat_in_rsc_rdy, widthIn, heightIn,
      pix_chan1_rsc_dat, pix_chan1_rsc_vld, pix_chan1_rsc_rdy, dy_chan_rsc_dat, dy_chan_rsc_vld,
      dy_chan_rsc_rdy, line_buf0_rsci_d_d, line_buf0_rsci_q_d, line_buf0_rsci_radr_d,
      line_buf0_rsci_wadr_d, line_buf1_rsci_d_d, line_buf1_rsci_q_d, line_buf1_rsci_radr_d,
      line_buf1_rsci_wadr_d, line_buf0_rsci_re_d_pff, line_buf0_rsci_we_d_pff, line_buf1_rsci_re_d_pff,
      line_buf1_rsci_we_d_pff
);
  input clk;
  input rst;
  input arst_n;
  input [33:0] dat_in_rsc_dat;
  input dat_in_rsc_vld;
  output dat_in_rsc_rdy;
  input [9:0] widthIn;
  input [8:0] heightIn;
  output [31:0] pix_chan1_rsc_dat;
  output pix_chan1_rsc_vld;
  input pix_chan1_rsc_rdy;
  output [35:0] dy_chan_rsc_dat;
  output dy_chan_rsc_vld;
  input dy_chan_rsc_rdy;
  output [63:0] line_buf0_rsci_d_d;
  input [63:0] line_buf0_rsci_q_d;
  output [6:0] line_buf0_rsci_radr_d;
  output [6:0] line_buf0_rsci_wadr_d;
  output [63:0] line_buf1_rsci_d_d;
  input [63:0] line_buf1_rsci_q_d;
  output [6:0] line_buf1_rsci_radr_d;
  output [6:0] line_buf1_rsci_wadr_d;
  output line_buf0_rsci_re_d_pff;
  output line_buf0_rsci_we_d_pff;
  output line_buf1_rsci_re_d_pff;
  output line_buf1_rsci_we_d_pff;


  // Interconnect Declarations
  wire run_wen;
  wire run_wten;
  wire dat_in_rsci_biwt;
  reg dat_in_rsci_iswt0;
  wire dat_in_rsci_wen_comp;
  wire [31:0] dat_in_rsci_idat_mxwt;
  wire pix_chan1_rsci_bawt;
  wire pix_chan1_rsci_wen_comp;
  reg [31:0] pix_chan1_rsci_idat;
  wire dy_chan_rsci_bawt;
  wire dy_chan_rsci_wen_comp;
  wire line_buf0_rsci_bawt;
  wire [63:0] line_buf0_rsci_q_d_mxwt;
  wire line_buf1_rsci_bawt;
  wire [63:0] line_buf1_rsci_q_d_mxwt;
  reg run_flen;
  reg [8:0] dy_chan_rsci_idat_35_27;
  wire [9:0] nl_dy_chan_rsci_idat_35_27;
  reg [8:0] dy_chan_rsci_idat_26_18;
  wire [9:0] nl_dy_chan_rsci_idat_26_18;
  reg [8:0] dy_chan_rsci_idat_17_9;
  wire [9:0] nl_dy_chan_rsci_idat_17_9;
  reg [8:0] dy_chan_rsci_idat_8_0;
  wire [9:0] nl_dy_chan_rsci_idat_8_0;
  reg [31:0] pix0_pix_lpi_3_dfm;
  reg [31:0] wrbuf0_pix_31_0_lpi_3;
  wire [3:0] fsm_output;
  wire VROW_equal_tmp;
  wire VCOL_equal_1_tmp;
  wire [9:0] VCOL_acc_9_tmp;
  wire [10:0] nl_VCOL_acc_9_tmp;
  wire VCOL_VCOL_or_tmp;
  wire nor_tmp_6;
  wire and_dcpl_6;
  wire nand_tmp_16;
  wire and_tmp_14;
  wire mux_tmp_51;
  wire mux_tmp_52;
  wire and_dcpl_14;
  wire and_dcpl_15;
  wire and_dcpl_17;
  wire or_dcpl_13;
  wire or_dcpl_14;
  wire or_tmp_40;
  wire mux_tmp_53;
  wire mux_tmp_54;
  wire and_tmp_16;
  wire or_dcpl_15;
  wire or_dcpl_16;
  wire not_tmp_70;
  wire or_tmp_47;
  wire mux_tmp_63;
  wire and_dcpl_24;
  wire or_dcpl_18;
  wire or_dcpl_19;
  wire or_dcpl_24;
  wire and_dcpl_30;
  wire or_dcpl_25;
  wire and_dcpl_33;
  wire and_dcpl_38;
  wire and_dcpl_41;
  wire mux_tmp_76;
  wire mux_tmp_78;
  wire or_tmp_67;
  wire mux_tmp_81;
  wire or_tmp_69;
  wire or_tmp_80;
  wire or_tmp_105;
  wire or_tmp_108;
  wire or_tmp_112;
  wire or_tmp_125;
  wire and_133_cse;
  reg VCOL_stage_v;
  wire VCOL_or_cse_1;
  wire VCOL_or_1_cse_1;
  reg [8:0] VROW_y_sva;
  reg VCOL_nor_1_itm_1;
  reg VCOL_stage_v_1;
  reg VCOL_stage_0_2;
  wire VCOL_nand_7_cse_1;
  reg VCOL_if_slc_operator_9_false_acc_9_svs_st_1;
  reg operator_10_false_operator_10_false_slc_VCOL_x_0_2_itm_1;
  reg VCOL_stage_en_3;
  wire VCOL_nand_2_cse_1;
  reg [8:0] VCOL_asn_4_itm_1;
  reg [8:0] VCOL_asn_4_itm_2;
  reg VCOL_stage_0_1;
  reg VCOL_stage_0;
  reg [9:0] VCOL_x_sva;
  reg VCOL_if_slc_operator_9_false_acc_9_svs_1;
  reg [8:0] VCOL_asn_4_itm;
  wire VCOL_if_5_and_1_cse;
  wire operator_10_false_and_cse;
  reg reg_line_buf1_rsci_readA_r_ram_ir_internal_RMASK_B_d_run_psct_cse;
  wire VCOL_and_14_cse;
  wire VCOL_and_11_cse;
  wire and_296_cse;
  wire and_267_cse;
  wire or_35_cse;
  wire and_268_cse;
  wire or_2_cse;
  reg reg_dy_chan_rsci_iswt0_cse;
  wire and_207_m1c;
  wire rdbuf0_pix_and_1_cse;
  wire [31:0] pix0_pix_mux1h_rmff;
  wire [31:0] wrbuf0_pix_mux_rmff;
  reg [6:0] line_buf0_rsci_radr_d_reg;
  wire [6:0] VCOL_if_2_mux_1_rmff;
  wire line_buf0_rsci_re_d_iff;
  wire and_226_rmff;
  reg [6:0] line_buf0_rsci_wadr_d_reg;
  wire [6:0] VCOL_if_2_mux_rmff;
  wire line_buf0_rsci_we_d_iff;
  reg [63:0] line_buf1_rsci_d_d_reg;
  wire [63:0] rdbuf0_pix_mux1h_rmff;
  reg [6:0] line_buf1_rsci_radr_d_reg;
  wire [6:0] VCOL_if_2_mux_2_rmff;
  wire line_buf1_rsci_re_d_iff;
  reg [6:0] line_buf1_rsci_wadr_d_reg;
  wire [6:0] VCOL_if_2_mux_3_rmff;
  wire line_buf1_rsci_we_d_iff;
  wire and_234_rmff;
  wire and_230_rmff;
  wire and_263_rmff;
  reg [63:0] rdbuf0_pix_lpi_3;
  wire VCOL_or_2_itm;
  reg [31:0] pix0_pix_lpi_3;
  reg [31:0] wrbuf0_pix_31_0_lpi_4;
  reg [31:0] pix0_pix_lpi_3_dfm_2;
  reg VCOL_stage_en_1;
  reg VCOL_stage_en_2;
  reg [31:0] VCOL_qelse_slc_rdbuf1_pix_63_32_itm_1;
  reg [31:0] rdbuf1_pix_lpi_3_63_32;
  wire [8:0] VROW_y_sva_mx0w2;
  wire [9:0] nl_VROW_y_sva_mx0w2;
  wire VCOL_stage_v_mx0c0;
  wire pix_chan1_rsci_idat_mx1c1;
  wire VCOL_stage_v_1_mx2c1;
  wire dat_in_rsci_iswt0_mx0c1;
  wire VCOL_stage_en_1_mx0w0;
  wire VCOL_stage_en_2_mx0w0;
  wire VCOL_stage_en_3_mx0w0;
  wire VCOL_stage_en_3_mx1c0;
  wire VCOL_stage_en_3_mx1c2;
  wire pix0_pix_lpi_3_mx1c1;
  wire [31:0] pix0_pix_lpi_3_dfm_2_mx1;
  wire [31:0] pix0_pix_lpi_3_dfm_1_mx0;
  wire [31:0] pix2_pix_lpi_3_dfm_1;
  wire [31:0] VCOL_qr_1_lpi_3_dfm_mx0;
  wire VCOL_VCOL_nand_tmp_1;
  wire [6:0] VCOL_x_sva_mx1_7_1;
  wire operator_9_false_acc_itm_9_1;

  wire[8:0] VROW_y_mux_1_nl;
  wire VCOL_not_8_nl;
  wire VROW_y_not_2_nl;
  wire not_281_nl;
  wire mux_55_nl;
  wire nand_17_nl;
  wire and_193_nl;
  wire and_195_nl;
  wire rdbuf0_pix_and_2_nl;
  wire rdbuf0_pix_or_nl;
  wire mux_79_nl;
  wire or_98_nl;
  wire nor_nl;
  wire VCOL_mux_11_nl;
  wire VCOL_mux_13_nl;
  wire VCOL_mux_15_nl;
  wire or_158_nl;
  wire rdbuf1_pix_and_1_nl;
  wire pix0_pix_pix0_pix_nor_nl;
  wire pix0_pix_and_3_nl;
  wire and_119_nl;
  wire[9:0] operator_9_false_acc_nl;
  wire[10:0] nl_operator_9_false_acc_nl;
  wire VCOL_and_4_nl;
  wire VCOL_and_1_nl;
  wire[8:0] operator_11_true_acc_nl;
  wire[9:0] nl_operator_11_true_acc_nl;
  wire and_43_nl;
  wire and_61_nl;
  wire mux_75_nl;
  wire or_92_nl;
  wire or_91_nl;
  wire or_96_nl;
  wire mux_77_nl;
  wire or_94_nl;
  wire mux_80_nl;
  wire mux_62_nl;
  wire mux_61_nl;
  wire mux_60_nl;
  wire mux_59_nl;
  wire and_308_nl;
  wire mux_84_nl;
  wire nand_20_nl;
  wire mux_83_nl;
  wire mux_82_nl;
  wire or_7_nl;

  // Interconnect Declarations for Component Instantiations 
  wire  nl_EdgeDetect_IP_EdgeDetect_VerDer_run_dat_in_rsci_inst_dat_in_rsci_oswt_unreg;
  assign nl_EdgeDetect_IP_EdgeDetect_VerDer_run_dat_in_rsci_inst_dat_in_rsci_oswt_unreg
      = mux_tmp_63 & and_dcpl_38 & (fsm_output[1]);
  wire [35:0] nl_EdgeDetect_IP_EdgeDetect_VerDer_run_dy_chan_rsci_inst_dy_chan_rsci_idat;
  assign nl_EdgeDetect_IP_EdgeDetect_VerDer_run_dy_chan_rsci_inst_dy_chan_rsci_idat
      = {dy_chan_rsci_idat_35_27 , dy_chan_rsci_idat_26_18 , dy_chan_rsci_idat_17_9
      , dy_chan_rsci_idat_8_0};
  wire  nl_EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf0_rsci_1_inst_line_buf0_rsci_iswt0_1_pff;
  assign nl_EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf0_rsci_1_inst_line_buf0_rsci_iswt0_1_pff
      = and_tmp_14 & and_dcpl_41 & VCOL_stage_0_2 & (fsm_output[1]);
  wire  nl_EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf1_rsci_1_inst_line_buf1_rsci_iswt0_1_pff;
  assign nl_EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf1_rsci_1_inst_line_buf1_rsci_iswt0_1_pff
      = (~ mux_tmp_78) & and_268_cse & (fsm_output[1]);
  EdgeDetect_IP_EdgeDetect_VerDer_run_dat_in_rsci EdgeDetect_IP_EdgeDetect_VerDer_run_dat_in_rsci_inst
      (
      .dat_in_rsc_dat(dat_in_rsc_dat),
      .dat_in_rsc_vld(dat_in_rsc_vld),
      .dat_in_rsc_rdy(dat_in_rsc_rdy),
      .run_wen(run_wen),
      .dat_in_rsci_oswt_unreg(nl_EdgeDetect_IP_EdgeDetect_VerDer_run_dat_in_rsci_inst_dat_in_rsci_oswt_unreg),
      .dat_in_rsci_biwt(dat_in_rsci_biwt),
      .dat_in_rsci_iswt0(dat_in_rsci_iswt0),
      .dat_in_rsci_wen_comp(dat_in_rsci_wen_comp),
      .dat_in_rsci_idat_mxwt(dat_in_rsci_idat_mxwt)
    );
  EdgeDetect_IP_EdgeDetect_VerDer_run_pix_chan1_rsci EdgeDetect_IP_EdgeDetect_VerDer_run_pix_chan1_rsci_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .pix_chan1_rsc_dat(pix_chan1_rsc_dat),
      .pix_chan1_rsc_vld(pix_chan1_rsc_vld),
      .pix_chan1_rsc_rdy(pix_chan1_rsc_rdy),
      .run_wen(run_wen),
      .pix_chan1_rsci_oswt_unreg(and_234_rmff),
      .pix_chan1_rsci_bawt(pix_chan1_rsci_bawt),
      .pix_chan1_rsci_iswt0(reg_dy_chan_rsci_iswt0_cse),
      .pix_chan1_rsci_wen_comp(pix_chan1_rsci_wen_comp),
      .pix_chan1_rsci_idat(pix_chan1_rsci_idat)
    );
  EdgeDetect_IP_EdgeDetect_VerDer_run_dy_chan_rsci EdgeDetect_IP_EdgeDetect_VerDer_run_dy_chan_rsci_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dy_chan_rsc_dat(dy_chan_rsc_dat),
      .dy_chan_rsc_vld(dy_chan_rsc_vld),
      .dy_chan_rsc_rdy(dy_chan_rsc_rdy),
      .run_wen(run_wen),
      .dy_chan_rsci_oswt_unreg(and_234_rmff),
      .dy_chan_rsci_bawt(dy_chan_rsci_bawt),
      .dy_chan_rsci_iswt0(reg_dy_chan_rsci_iswt0_cse),
      .dy_chan_rsci_wen_comp(dy_chan_rsci_wen_comp),
      .dy_chan_rsci_idat(nl_EdgeDetect_IP_EdgeDetect_VerDer_run_dy_chan_rsci_inst_dy_chan_rsci_idat[35:0])
    );
  EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf0_rsci_1 EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf0_rsci_1_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .line_buf0_rsci_q_d(line_buf0_rsci_q_d),
      .run_wen(run_wen),
      .run_wten(run_wten),
      .line_buf0_rsci_oswt_unreg(and_230_rmff),
      .line_buf0_rsci_bawt(line_buf0_rsci_bawt),
      .line_buf0_rsci_iswt0(reg_line_buf1_rsci_readA_r_ram_ir_internal_RMASK_B_d_run_psct_cse),
      .line_buf0_rsci_q_d_mxwt(line_buf0_rsci_q_d_mxwt),
      .line_buf0_rsci_re_d_pff(line_buf0_rsci_re_d_iff),
      .line_buf0_rsci_iswt0_pff(and_226_rmff),
      .line_buf0_rsci_we_d_pff(line_buf0_rsci_we_d_iff),
      .line_buf0_rsci_iswt0_1_pff(nl_EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf0_rsci_1_inst_line_buf0_rsci_iswt0_1_pff)
    );
  EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf1_rsci_1 EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf1_rsci_1_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .line_buf1_rsci_q_d(line_buf1_rsci_q_d),
      .run_wen(run_wen),
      .run_wten(run_wten),
      .line_buf1_rsci_oswt_unreg(and_230_rmff),
      .line_buf1_rsci_bawt(line_buf1_rsci_bawt),
      .line_buf1_rsci_iswt0(reg_line_buf1_rsci_readA_r_ram_ir_internal_RMASK_B_d_run_psct_cse),
      .line_buf1_rsci_q_d_mxwt(line_buf1_rsci_q_d_mxwt),
      .line_buf1_rsci_re_d_pff(line_buf1_rsci_re_d_iff),
      .line_buf1_rsci_iswt0_pff(and_226_rmff),
      .line_buf1_rsci_we_d_pff(line_buf1_rsci_we_d_iff),
      .line_buf1_rsci_iswt0_1_pff(nl_EdgeDetect_IP_EdgeDetect_VerDer_run_line_buf1_rsci_1_inst_line_buf1_rsci_iswt0_1_pff)
    );
  EdgeDetect_IP_EdgeDetect_VerDer_run_staller EdgeDetect_IP_EdgeDetect_VerDer_run_staller_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .run_wen(run_wen),
      .run_wten(run_wten),
      .dat_in_rsci_wen_comp(dat_in_rsci_wen_comp),
      .pix_chan1_rsci_wen_comp(pix_chan1_rsci_wen_comp),
      .dy_chan_rsci_wen_comp(dy_chan_rsci_wen_comp),
      .run_flen_unreg(and_263_rmff)
    );
  EdgeDetect_IP_EdgeDetect_VerDer_run_run_fsm EdgeDetect_IP_EdgeDetect_VerDer_run_run_fsm_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .run_wen(run_wen),
      .fsm_output(fsm_output),
      .VCOL_C_0_tr0(and_dcpl_6),
      .VROW_C_0_tr0(VROW_equal_tmp)
    );
  assign VCOL_if_5_and_1_cse = run_wen & (~((~ (fsm_output[1])) | (~(or_2_cse & nand_tmp_16))
      | and_dcpl_15 | or_dcpl_19));
  assign or_2_cse = (VCOL_asn_4_itm_1!=9'b000000000);
  assign VCOL_and_11_cse = run_wen & mux_tmp_52;
  assign operator_10_false_and_cse = run_wen & (~((~ (fsm_output[1])) | or_dcpl_16));
  assign and_193_nl = and_tmp_14 & and_dcpl_41 & VCOL_stage_0_2 & VCOL_if_slc_operator_9_false_acc_9_svs_1
      & (fsm_output[1]);
  assign and_195_nl = and_tmp_14 & and_dcpl_41 & VCOL_stage_0_2 & (~ VCOL_if_slc_operator_9_false_acc_9_svs_1)
      & (fsm_output[1]);
  assign pix0_pix_mux1h_rmff = MUX1HOT_v_32_3_2(pix0_pix_lpi_3, dat_in_rsci_idat_mxwt,
      pix0_pix_lpi_3_dfm, {and_193_nl , and_195_nl , or_tmp_105});
  assign wrbuf0_pix_mux_rmff = MUX_v_32_2_2(wrbuf0_pix_31_0_lpi_4, wrbuf0_pix_31_0_lpi_3,
      or_tmp_105);
  assign VCOL_if_2_mux_rmff = MUX_v_7_2_2((VCOL_x_sva[7:1]), line_buf0_rsci_wadr_d_reg,
      or_tmp_105);
  assign VCOL_if_2_mux_1_rmff = MUX_v_7_2_2(VCOL_x_sva_mx1_7_1, line_buf0_rsci_radr_d_reg,
      or_tmp_108);
  assign VCOL_if_2_mux_2_rmff = MUX_v_7_2_2(VCOL_x_sva_mx1_7_1, line_buf1_rsci_radr_d_reg,
      or_tmp_108);
  assign and_207_m1c = mux_tmp_51 & nor_tmp_6 & (~ VCOL_equal_1_tmp) & VCOL_stage_0_1
      & (VCOL_acc_9_tmp[0]) & VCOL_stage_v & (fsm_output[1]);
  assign rdbuf0_pix_and_2_nl = (~ (VCOL_x_sva[0])) & and_207_m1c;
  assign rdbuf0_pix_or_nl = ((VCOL_x_sva[0]) & and_207_m1c) | (nand_tmp_16 & (~ VCOL_stage_v_1)
      & VCOL_stage_0_1 & (VCOL_x_sva[0]) & VCOL_stage_v & (fsm_output[1]));
  assign rdbuf0_pix_mux1h_rmff = MUX1HOT_v_64_3_2(line_buf0_rsci_q_d_mxwt, rdbuf0_pix_lpi_3,
      line_buf1_rsci_d_d_reg, {rdbuf0_pix_and_2_nl , rdbuf0_pix_or_nl , or_tmp_112});
  assign VCOL_if_2_mux_3_rmff = MUX_v_7_2_2(VCOL_x_sva_mx1_7_1, line_buf1_rsci_wadr_d_reg,
      or_tmp_112);
  assign VCOL_mux_11_nl = MUX_s_1_2_2(VCOL_stage_en_1, VCOL_stage_en_1_mx0w0, fsm_output[1]);
  assign VCOL_mux_13_nl = MUX_s_1_2_2(VCOL_stage_en_2, VCOL_stage_en_2_mx0w0, fsm_output[1]);
  assign VCOL_mux_15_nl = MUX_s_1_2_2(VCOL_stage_en_3, VCOL_stage_en_3_mx0w0, fsm_output[1]);
  assign nor_nl = ~(((~(VCOL_stage_v & ((fsm_output[3]) | (or_dcpl_16 & (fsm_output[1])))))
      & ((VCOL_stage_0 & (~(and_tmp_16 & (fsm_output[1])))) | and_133_cse)) | VCOL_mux_11_nl
      | VCOL_mux_13_nl | VCOL_mux_15_nl);
  assign or_158_nl = (fsm_output[3]) | (VROW_equal_tmp & (fsm_output[2]));
  assign and_263_rmff = MUX_s_1_2_2(nor_nl, run_flen, or_158_nl);
  assign and_226_rmff = (~ mux_tmp_76) & and_268_cse & (fsm_output[1]);
  assign and_230_rmff = and_tmp_14 & line_buf1_rsci_bawt & line_buf0_rsci_bawt &
      (~ operator_10_false_operator_10_false_slc_VCOL_x_0_2_itm_1) & nor_tmp_6 &
      (fsm_output[1]);
  assign and_234_rmff = VCOL_VCOL_or_tmp & VCOL_stage_en_3 & or_35_cse & (fsm_output[1]);
  assign VCOL_and_14_cse = run_wen & (~ or_tmp_125);
  assign rdbuf0_pix_and_1_cse = run_wen & (~ or_dcpl_14) & (~ (VCOL_x_sva[0]));
  assign and_296_cse = dy_chan_rsci_bawt & pix_chan1_rsci_bawt;
  assign nl_VROW_y_sva_mx0w2 = VROW_y_sva + 9'b000000001;
  assign VROW_y_sva_mx0w2 = nl_VROW_y_sva_mx0w2[8:0];
  assign nl_VCOL_acc_9_tmp = VCOL_x_sva + 10'b0000000001;
  assign VCOL_acc_9_tmp = nl_VCOL_acc_9_tmp[9:0];
  assign VCOL_x_sva_mx1_7_1 = MUX_v_7_2_2((VCOL_x_sva[7:1]), (VCOL_acc_9_tmp[7:1]),
      VCOL_stage_v_1);
  assign nl_operator_9_false_acc_nl = ({1'b1 , heightIn}) + conv_u2s_9_10(~ VROW_y_sva);
  assign operator_9_false_acc_nl = nl_operator_9_false_acc_nl[9:0];
  assign operator_9_false_acc_itm_9_1 = readslicef_10_1_9(operator_9_false_acc_nl);
  assign VCOL_stage_en_1_mx0w0 = VCOL_stage_v & (~(VCOL_stage_v_1 & or_dcpl_25))
      & VCOL_stage_0_1 & or_dcpl_24 & VCOL_or_cse_1 & VCOL_or_1_cse_1;
  assign VCOL_or_2_itm = dat_in_rsci_biwt | VCOL_if_slc_operator_9_false_acc_9_svs_st_1;
  assign VCOL_stage_en_2_mx0w0 = VCOL_stage_v_1 & VCOL_stage_0_2 & VCOL_or_2_itm
      & (line_buf1_rsci_bawt | VCOL_nand_7_cse_1) & (line_buf0_rsci_bawt | VCOL_nand_7_cse_1)
      & VCOL_or_cse_1 & VCOL_or_1_cse_1;
  assign VCOL_stage_en_3_mx0w0 = VCOL_stage_en_3 & VCOL_or_cse_1 & VCOL_or_1_cse_1;
  assign pix0_pix_lpi_3_dfm_2_mx1 = MUX_v_32_2_2(pix0_pix_lpi_3_dfm_1_mx0, VCOL_qr_1_lpi_3_dfm_mx0,
      VROW_equal_tmp);
  assign pix0_pix_lpi_3_dfm_1_mx0 = MUX_v_32_2_2(dat_in_rsci_idat_mxwt, pix0_pix_lpi_3,
      VCOL_if_slc_operator_9_false_acc_9_svs_1);
  assign VCOL_and_4_nl = (~ (VCOL_x_sva[0])) & VCOL_VCOL_nand_tmp_1;
  assign VCOL_and_1_nl = (VCOL_x_sva[0]) & VCOL_VCOL_nand_tmp_1;
  assign pix2_pix_lpi_3_dfm_1 = MUX1HOT_v_32_3_2(VCOL_qr_1_lpi_3_dfm_mx0, (line_buf1_rsci_q_d_mxwt[31:0]),
      VCOL_qelse_slc_rdbuf1_pix_63_32_itm_1, {(~ VCOL_VCOL_nand_tmp_1) , VCOL_and_4_nl
      , VCOL_and_1_nl});
  assign VCOL_qr_1_lpi_3_dfm_mx0 = MUX_v_32_2_2((line_buf0_rsci_q_d_mxwt[31:0]),
      (rdbuf0_pix_lpi_3[63:32]), VCOL_x_sva[0]);
  assign VCOL_VCOL_nand_tmp_1 = ~((VROW_y_sva[0]) & VCOL_nor_1_itm_1);
  assign VCOL_or_cse_1 = pix_chan1_rsci_bawt | VCOL_nand_2_cse_1;
  assign VCOL_or_1_cse_1 = dy_chan_rsci_bawt | VCOL_nand_2_cse_1;
  assign VCOL_nand_7_cse_1 = ~((~ operator_10_false_operator_10_false_slc_VCOL_x_0_2_itm_1)
      & VCOL_stage_v_1);
  assign VCOL_VCOL_or_tmp = (VCOL_asn_4_itm_2!=9'b000000000);
  assign VCOL_nand_2_cse_1 = ~(VCOL_VCOL_or_tmp & VCOL_stage_en_3);
  assign VROW_equal_tmp = VROW_y_sva == heightIn;
  assign nl_operator_11_true_acc_nl = conv_u2s_8_9(widthIn[9:2]) + 9'b111111111;
  assign operator_11_true_acc_nl = nl_operator_11_true_acc_nl[8:0];
  assign VCOL_equal_1_tmp = VCOL_x_sva == (signext_10_9(operator_11_true_acc_nl));
  assign nor_tmp_6 = VCOL_stage_0_2 & VCOL_stage_v_1;
  assign and_267_cse = line_buf0_rsci_bawt & line_buf1_rsci_bawt;
  assign and_268_cse = VCOL_stage_0_1 & VCOL_stage_v;
  assign or_35_cse = and_296_cse | (~ VCOL_VCOL_or_tmp);
  assign and_dcpl_6 = or_35_cse & VCOL_stage_en_3 & (~(VCOL_stage_0_2 | VCOL_stage_0
      | VCOL_stage_0_1));
  assign nand_tmp_16 = ~(VCOL_stage_en_3 & VCOL_VCOL_or_tmp & (~ and_296_cse));
  assign and_tmp_14 = VCOL_or_2_itm & nand_tmp_16;
  assign and_43_nl = and_267_cse & and_tmp_14;
  assign mux_tmp_51 = MUX_s_1_2_2(and_43_nl, and_tmp_14, operator_10_false_operator_10_false_slc_VCOL_x_0_2_itm_1);
  assign mux_tmp_52 = MUX_s_1_2_2(nand_tmp_16, mux_tmp_51, VCOL_stage_v_1);
  assign and_dcpl_14 = ~(and_267_cse | operator_10_false_operator_10_false_slc_VCOL_x_0_2_itm_1);
  assign and_dcpl_15 = ~(dat_in_rsci_biwt | VCOL_if_slc_operator_9_false_acc_9_svs_st_1);
  assign and_dcpl_17 = (~ and_296_cse) & VCOL_VCOL_or_tmp & VCOL_stage_en_3;
  assign or_dcpl_13 = and_dcpl_17 | and_dcpl_15;
  assign or_dcpl_14 = or_dcpl_13 | and_dcpl_14 | (~ VCOL_stage_v_1);
  assign or_tmp_40 = VCOL_stage_v_1 | and_dcpl_17;
  assign mux_tmp_53 = MUX_s_1_2_2((~ or_tmp_40), mux_tmp_52, VCOL_stage_0_2);
  assign mux_tmp_54 = MUX_s_1_2_2((~ mux_tmp_53), or_tmp_40, VCOL_equal_1_tmp);
  assign and_tmp_16 = VCOL_equal_1_tmp & VCOL_stage_0_2 & VCOL_stage_v_1 & mux_tmp_51;
  assign or_dcpl_15 = ~(VCOL_stage_0_1 & VCOL_stage_v);
  assign or_dcpl_16 = mux_tmp_54 | or_dcpl_15;
  assign not_tmp_70 = ~(VCOL_VCOL_or_tmp & or_35_cse);
  assign or_tmp_47 = VCOL_or_2_itm | not_tmp_70;
  assign and_61_nl = and_267_cse & nand_tmp_16;
  assign mux_tmp_63 = MUX_s_1_2_2(and_61_nl, nand_tmp_16, operator_10_false_operator_10_false_slc_VCOL_x_0_2_itm_1);
  assign and_dcpl_24 = or_2_cse & mux_tmp_63 & VCOL_or_2_itm;
  assign or_dcpl_18 = ~(VCOL_stage_v_1 & VCOL_stage_0_2);
  assign or_dcpl_19 = and_dcpl_14 | or_dcpl_18;
  assign or_dcpl_24 = or_dcpl_13 | and_dcpl_14 | or_dcpl_18 | (~ VCOL_equal_1_tmp);
  assign and_dcpl_30 = (~ mux_tmp_54) & and_268_cse;
  assign or_dcpl_25 = or_dcpl_13 | or_dcpl_19;
  assign and_dcpl_33 = (~ and_296_cse) & VCOL_VCOL_or_tmp;
  assign and_dcpl_38 = dat_in_rsci_biwt & (~ VCOL_if_slc_operator_9_false_acc_9_svs_st_1)
      & nor_tmp_6;
  assign and_dcpl_41 = operator_10_false_operator_10_false_slc_VCOL_x_0_2_itm_1 &
      VCOL_stage_v_1;
  assign or_92_nl = (VCOL_acc_9_tmp[0]) | VCOL_equal_1_tmp;
  assign mux_75_nl = MUX_s_1_2_2((~ mux_tmp_53), or_tmp_40, or_92_nl);
  assign or_91_nl = (VCOL_acc_9_tmp[0]) | VCOL_equal_1_tmp | or_dcpl_25;
  assign mux_tmp_76 = MUX_s_1_2_2(mux_75_nl, or_91_nl, VCOL_x_sva[0]);
  assign or_96_nl = (~ (VCOL_acc_9_tmp[0])) | VCOL_equal_1_tmp | or_dcpl_25;
  assign or_94_nl = (~ (VCOL_acc_9_tmp[0])) | VCOL_equal_1_tmp;
  assign mux_77_nl = MUX_s_1_2_2((~ mux_tmp_53), or_tmp_40, or_94_nl);
  assign mux_tmp_78 = MUX_s_1_2_2(or_96_nl, mux_77_nl, VCOL_x_sva[0]);
  assign or_tmp_67 = VCOL_or_2_itm | and_dcpl_33;
  assign mux_80_nl = MUX_s_1_2_2(and_dcpl_33, or_tmp_67, and_267_cse);
  assign mux_tmp_81 = MUX_s_1_2_2(mux_80_nl, or_tmp_67, operator_10_false_operator_10_false_slc_VCOL_x_0_2_itm_1);
  assign or_tmp_69 = (fsm_output[0]) | (fsm_output[3]);
  assign and_133_cse = (fsm_output[0]) | (fsm_output[2]);
  assign mux_59_nl = MUX_s_1_2_2(not_tmp_70, or_tmp_47, and_267_cse);
  assign mux_60_nl = MUX_s_1_2_2(mux_59_nl, or_tmp_47, operator_10_false_operator_10_false_slc_VCOL_x_0_2_itm_1);
  assign and_308_nl = or_2_cse & VCOL_stage_v_1;
  assign mux_61_nl = MUX_s_1_2_2(not_tmp_70, mux_60_nl, and_308_nl);
  assign mux_62_nl = MUX_s_1_2_2(not_tmp_70, mux_61_nl, VCOL_stage_0_2);
  assign or_tmp_80 = (~ mux_62_nl) & VCOL_stage_en_3 & (fsm_output[1]);
  assign or_tmp_105 = (~ (fsm_output[1])) | or_dcpl_13 | (~(operator_10_false_operator_10_false_slc_VCOL_x_0_2_itm_1
      & VCOL_stage_v_1 & VCOL_stage_0_2));
  assign or_tmp_108 = (~ (fsm_output[1])) | mux_tmp_76 | or_dcpl_15;
  assign or_tmp_112 = (~ (fsm_output[1])) | mux_tmp_78 | or_dcpl_15;
  assign or_tmp_125 = (fsm_output[3:2]!=2'b00);
  assign VCOL_stage_v_mx0c0 = (~ mux_tmp_54) & and_268_cse & (~ VCOL_stage_0) & (fsm_output[1]);
  assign pix_chan1_rsci_idat_mx1c1 = and_dcpl_24 & nor_tmp_6 & (~ (VCOL_x_sva[0]));
  assign VCOL_stage_v_1_mx2c1 = mux_tmp_51 & (VCOL_equal_1_tmp | (~ VCOL_stage_0_1)
      | (~ VCOL_stage_v)) & nor_tmp_6;
  assign dat_in_rsci_iswt0_mx0c1 = ((~ VCOL_stage_v) | operator_9_false_acc_itm_9_1
      | (~ VCOL_stage_0_1) | VCOL_equal_1_tmp) & mux_tmp_63 & and_dcpl_38 & (fsm_output[1]);
  assign mux_83_nl = MUX_s_1_2_2(and_dcpl_33, mux_tmp_81, VCOL_stage_v_1);
  assign nand_20_nl = ~(VCOL_stage_0_2 & (~ mux_83_nl));
  assign mux_82_nl = MUX_s_1_2_2(and_dcpl_33, mux_tmp_81, nor_tmp_6);
  assign or_7_nl = VCOL_stage_0 | VCOL_stage_0_1;
  assign mux_84_nl = MUX_s_1_2_2(nand_20_nl, mux_82_nl, or_7_nl);
  assign VCOL_stage_en_3_mx1c0 = ((~ mux_84_nl) & VCOL_stage_en_3 & (fsm_output[1]))
      | ((~ VROW_equal_tmp) & (fsm_output[2])) | (fsm_output[0]);
  assign VCOL_stage_en_3_mx1c2 = nor_tmp_6 & mux_tmp_51 & (fsm_output[1]);
  assign pix0_pix_lpi_3_mx1c1 = mux_tmp_51 & VCOL_stage_v_1 & (~ VROW_equal_tmp);
  assign line_buf0_rsci_d_d = {pix0_pix_mux1h_rmff , wrbuf0_pix_mux_rmff};
  assign line_buf0_rsci_radr_d = VCOL_if_2_mux_1_rmff;
  assign line_buf0_rsci_re_d_pff = line_buf0_rsci_re_d_iff;
  assign line_buf0_rsci_wadr_d = VCOL_if_2_mux_rmff;
  assign line_buf0_rsci_we_d_pff = line_buf0_rsci_we_d_iff;
  assign line_buf1_rsci_d_d = rdbuf0_pix_mux1h_rmff;
  assign line_buf1_rsci_radr_d = VCOL_if_2_mux_2_rmff;
  assign line_buf1_rsci_re_d_pff = line_buf1_rsci_re_d_iff;
  assign line_buf1_rsci_wadr_d = VCOL_if_2_mux_3_rmff;
  assign line_buf1_rsci_we_d_pff = line_buf1_rsci_we_d_iff;
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_asn_4_itm <= 9'b000000000;
    end
    else if ( rst ) begin
      VCOL_asn_4_itm <= 9'b000000000;
    end
    else if ( run_wen & ((~((~ mux_tmp_52) & VCOL_stage_v)) | or_tmp_69 | (fsm_output[2]))
        ) begin
      VCOL_asn_4_itm <= MUX_v_9_2_2(9'b000000000, VROW_y_mux_1_nl, VCOL_not_8_nl);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VROW_y_sva <= 9'b000000000;
    end
    else if ( rst ) begin
      VROW_y_sva <= 9'b000000000;
    end
    else if ( run_wen & (or_tmp_69 | (fsm_output[2])) ) begin
      VROW_y_sva <= MUX_v_9_2_2(9'b000000000, VROW_y_sva_mx0w2, VROW_y_not_2_nl);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_x_sva <= 10'b0000000000;
    end
    else if ( rst ) begin
      VCOL_x_sva <= 10'b0000000000;
    end
    else if ( run_wen & ((~ or_dcpl_14) | and_133_cse) ) begin
      VCOL_x_sva <= MUX_v_10_2_2(10'b0000000000, VCOL_acc_9_tmp, not_281_nl);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_stage_v <= 1'b0;
    end
    else if ( rst ) begin
      VCOL_stage_v <= 1'b0;
    end
    else if ( run_wen & (VCOL_stage_v_mx0c0 | ((~ mux_55_nl) & VCOL_stage_0 & (fsm_output[1]))
        | and_133_cse) ) begin
      VCOL_stage_v <= ~ VCOL_stage_v_mx0c0;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      reg_dy_chan_rsci_iswt0_cse <= 1'b0;
    end
    else if ( rst ) begin
      reg_dy_chan_rsci_iswt0_cse <= 1'b0;
    end
    else if ( run_wen & (or_tmp_80 | (and_dcpl_24 & nor_tmp_6 & (fsm_output[1])))
        ) begin
      reg_dy_chan_rsci_iswt0_cse <= ~ or_tmp_80;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      dy_chan_rsci_idat_35_27 <= 9'b000000000;
      dy_chan_rsci_idat_8_0 <= 9'b000000000;
      dy_chan_rsci_idat_26_18 <= 9'b000000000;
      dy_chan_rsci_idat_17_9 <= 9'b000000000;
    end
    else if ( rst ) begin
      dy_chan_rsci_idat_35_27 <= 9'b000000000;
      dy_chan_rsci_idat_8_0 <= 9'b000000000;
      dy_chan_rsci_idat_26_18 <= 9'b000000000;
      dy_chan_rsci_idat_17_9 <= 9'b000000000;
    end
    else if ( VCOL_if_5_and_1_cse ) begin
      dy_chan_rsci_idat_35_27 <= nl_dy_chan_rsci_idat_35_27[8:0];
      dy_chan_rsci_idat_8_0 <= nl_dy_chan_rsci_idat_8_0[8:0];
      dy_chan_rsci_idat_26_18 <= nl_dy_chan_rsci_idat_26_18[8:0];
      dy_chan_rsci_idat_17_9 <= nl_dy_chan_rsci_idat_17_9[8:0];
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_chan1_rsci_idat <= 32'b00000000000000000000000000000000;
    end
    else if ( rst ) begin
      pix_chan1_rsci_idat <= 32'b00000000000000000000000000000000;
    end
    else if ( run_wen & ((and_dcpl_24 & nor_tmp_6 & (VCOL_x_sva[0])) | pix_chan1_rsci_idat_mx1c1)
        & (fsm_output[1]) ) begin
      pix_chan1_rsci_idat <= MUX_v_32_2_2((rdbuf0_pix_lpi_3[63:32]), (line_buf0_rsci_q_d_mxwt[31:0]),
          pix_chan1_rsci_idat_mx1c1);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_stage_0_1 <= 1'b0;
    end
    else if ( rst ) begin
      VCOL_stage_0_1 <= 1'b0;
    end
    else if ( run_wen & (and_dcpl_30 | and_tmp_16 | and_133_cse) ) begin
      VCOL_stage_0_1 <= (VCOL_stage_0 & (~ and_tmp_16)) | and_133_cse;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_stage_0 <= 1'b0;
    end
    else if ( rst ) begin
      VCOL_stage_0 <= 1'b0;
    end
    else if ( run_wen & ((~ or_dcpl_24) | and_133_cse) ) begin
      VCOL_stage_0 <= and_133_cse;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_stage_v_1 <= 1'b0;
    end
    else if ( rst ) begin
      VCOL_stage_v_1 <= 1'b0;
    end
    else if ( run_wen & (and_dcpl_30 | VCOL_stage_v_1_mx2c1 | and_133_cse) ) begin
      VCOL_stage_v_1 <= ~(VCOL_stage_v_1_mx2c1 | and_133_cse);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_asn_4_itm_1 <= 9'b000000000;
      VCOL_nor_1_itm_1 <= 1'b0;
      VCOL_if_slc_operator_9_false_acc_9_svs_1 <= 1'b0;
    end
    else if ( rst ) begin
      VCOL_asn_4_itm_1 <= 9'b000000000;
      VCOL_nor_1_itm_1 <= 1'b0;
      VCOL_if_slc_operator_9_false_acc_9_svs_1 <= 1'b0;
    end
    else if ( VCOL_and_11_cse ) begin
      VCOL_asn_4_itm_1 <= VCOL_asn_4_itm;
      VCOL_nor_1_itm_1 <= ~((VROW_y_sva[8:1]!=8'b00000000));
      VCOL_if_slc_operator_9_false_acc_9_svs_1 <= operator_9_false_acc_itm_9_1;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      operator_10_false_operator_10_false_slc_VCOL_x_0_2_itm_1 <= 1'b0;
      VCOL_if_slc_operator_9_false_acc_9_svs_st_1 <= 1'b0;
    end
    else if ( rst ) begin
      operator_10_false_operator_10_false_slc_VCOL_x_0_2_itm_1 <= 1'b0;
      VCOL_if_slc_operator_9_false_acc_9_svs_st_1 <= 1'b0;
    end
    else if ( operator_10_false_and_cse ) begin
      operator_10_false_operator_10_false_slc_VCOL_x_0_2_itm_1 <= MUX_s_1_2_2((VCOL_x_sva[0]),
          (VCOL_acc_9_tmp[0]), VCOL_stage_v_1);
      VCOL_if_slc_operator_9_false_acc_9_svs_st_1 <= operator_9_false_acc_itm_9_1;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_asn_4_itm_2 <= 9'b000000000;
    end
    else if ( rst ) begin
      VCOL_asn_4_itm_2 <= 9'b000000000;
    end
    else if ( run_wen & (~((~ (fsm_output[1])) | or_dcpl_25)) ) begin
      VCOL_asn_4_itm_2 <= VCOL_asn_4_itm_1;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      dat_in_rsci_iswt0 <= 1'b0;
    end
    else if ( rst ) begin
      dat_in_rsci_iswt0 <= 1'b0;
    end
    else if ( run_wen & (((~ mux_tmp_54) & VCOL_stage_0_1 & (~ operator_9_false_acc_itm_9_1)
        & VCOL_stage_v & (fsm_output[1])) | dat_in_rsci_iswt0_mx0c1) ) begin
      dat_in_rsci_iswt0 <= ~ dat_in_rsci_iswt0_mx0c1;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix0_pix_lpi_3_dfm <= 32'b00000000000000000000000000000000;
      wrbuf0_pix_31_0_lpi_3 <= 32'b00000000000000000000000000000000;
      line_buf0_rsci_wadr_d_reg <= 7'b0000000;
      line_buf0_rsci_radr_d_reg <= 7'b0000000;
      line_buf1_rsci_radr_d_reg <= 7'b0000000;
      line_buf1_rsci_d_d_reg <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
      line_buf1_rsci_wadr_d_reg <= 7'b0000000;
      run_flen <= 1'b0;
      reg_line_buf1_rsci_readA_r_ram_ir_internal_RMASK_B_d_run_psct_cse <= 1'b0;
    end
    else if ( rst ) begin
      pix0_pix_lpi_3_dfm <= 32'b00000000000000000000000000000000;
      wrbuf0_pix_31_0_lpi_3 <= 32'b00000000000000000000000000000000;
      line_buf0_rsci_wadr_d_reg <= 7'b0000000;
      line_buf0_rsci_radr_d_reg <= 7'b0000000;
      line_buf1_rsci_radr_d_reg <= 7'b0000000;
      line_buf1_rsci_d_d_reg <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
      line_buf1_rsci_wadr_d_reg <= 7'b0000000;
      run_flen <= 1'b0;
      reg_line_buf1_rsci_readA_r_ram_ir_internal_RMASK_B_d_run_psct_cse <= 1'b0;
    end
    else if ( run_wen ) begin
      pix0_pix_lpi_3_dfm <= pix0_pix_mux1h_rmff;
      wrbuf0_pix_31_0_lpi_3 <= wrbuf0_pix_mux_rmff;
      line_buf0_rsci_wadr_d_reg <= VCOL_if_2_mux_rmff;
      line_buf0_rsci_radr_d_reg <= VCOL_if_2_mux_1_rmff;
      line_buf1_rsci_radr_d_reg <= VCOL_if_2_mux_2_rmff;
      line_buf1_rsci_d_d_reg <= rdbuf0_pix_mux1h_rmff;
      line_buf1_rsci_wadr_d_reg <= VCOL_if_2_mux_3_rmff;
      run_flen <= and_263_rmff;
      reg_line_buf1_rsci_readA_r_ram_ir_internal_RMASK_B_d_run_psct_cse <= and_226_rmff;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_stage_0_2 <= 1'b0;
    end
    else if ( rst ) begin
      VCOL_stage_0_2 <= 1'b0;
    end
    else if ( run_wen & (and_tmp_16 | (~ mux_79_nl) | and_133_cse) ) begin
      VCOL_stage_0_2 <= VCOL_stage_0_1 & (~ and_tmp_16) & (~ and_133_cse);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_stage_en_1 <= 1'b0;
      VCOL_stage_en_2 <= 1'b0;
    end
    else if ( rst ) begin
      VCOL_stage_en_1 <= 1'b0;
      VCOL_stage_en_2 <= 1'b0;
    end
    else if ( VCOL_and_14_cse ) begin
      VCOL_stage_en_1 <= VCOL_stage_en_1_mx0w0;
      VCOL_stage_en_2 <= VCOL_stage_en_2_mx0w0;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_stage_en_3 <= 1'b0;
    end
    else if ( rst ) begin
      VCOL_stage_en_3 <= 1'b0;
    end
    else if ( run_wen & (VCOL_stage_en_3_mx1c0 | (and_dcpl_6 & (fsm_output[1])) |
        VCOL_stage_en_3_mx1c2) ) begin
      VCOL_stage_en_3 <= (VCOL_stage_en_3_mx0w0 & (~ VCOL_stage_en_3_mx1c0)) | VCOL_stage_en_3_mx1c2;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      rdbuf0_pix_lpi_3 <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
      rdbuf1_pix_lpi_3_63_32 <= 32'b00000000000000000000000000000000;
    end
    else if ( rst ) begin
      rdbuf0_pix_lpi_3 <= 64'b0000000000000000000000000000000000000000000000000000000000000000;
      rdbuf1_pix_lpi_3_63_32 <= 32'b00000000000000000000000000000000;
    end
    else if ( rdbuf0_pix_and_1_cse ) begin
      rdbuf0_pix_lpi_3 <= line_buf0_rsci_q_d_mxwt;
      rdbuf1_pix_lpi_3_63_32 <= line_buf1_rsci_q_d_mxwt[63:32];
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      wrbuf0_pix_31_0_lpi_4 <= 32'b00000000000000000000000000000000;
    end
    else if ( rst ) begin
      wrbuf0_pix_31_0_lpi_4 <= 32'b00000000000000000000000000000000;
    end
    else if ( run_wen & (~(and_dcpl_17 | and_dcpl_15 | (VCOL_x_sva[0]))) ) begin
      wrbuf0_pix_31_0_lpi_4 <= pix0_pix_lpi_3_dfm_1_mx0;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      VCOL_qelse_slc_rdbuf1_pix_63_32_itm_1 <= 32'b00000000000000000000000000000000;
    end
    else if ( rst ) begin
      VCOL_qelse_slc_rdbuf1_pix_63_32_itm_1 <= 32'b00000000000000000000000000000000;
    end
    else if ( run_wen & (mux_tmp_51 | (~ VCOL_stage_v_1)) ) begin
      VCOL_qelse_slc_rdbuf1_pix_63_32_itm_1 <= MUX_v_32_2_2(rdbuf1_pix_lpi_3_63_32,
          (line_buf1_rsci_q_d_mxwt[63:32]), rdbuf1_pix_and_1_nl);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix0_pix_lpi_3 <= 32'b00000000000000000000000000000000;
    end
    else if ( rst ) begin
      pix0_pix_lpi_3 <= 32'b00000000000000000000000000000000;
    end
    else if ( run_wen & ((mux_tmp_51 & VCOL_stage_v_1 & VROW_equal_tmp) | pix0_pix_lpi_3_mx1c1
        | and_133_cse) ) begin
      pix0_pix_lpi_3 <= MUX1HOT_v_32_3_2(VCOL_qr_1_lpi_3_dfm_mx0, pix0_pix_lpi_3_dfm_1_mx0,
          pix0_pix_lpi_3_dfm_2, {pix0_pix_pix0_pix_nor_nl , pix0_pix_and_3_nl , and_133_cse});
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix0_pix_lpi_3_dfm_2 <= 32'b00000000000000000000000000000000;
    end
    else if ( rst ) begin
      pix0_pix_lpi_3_dfm_2 <= 32'b00000000000000000000000000000000;
    end
    else if ( run_wen & VCOL_stage_0_2 & (~ or_tmp_125) ) begin
      pix0_pix_lpi_3_dfm_2 <= MUX_v_32_2_2(VCOL_qr_1_lpi_3_dfm_mx0, pix0_pix_lpi_3_dfm_1_mx0,
          and_119_nl);
    end
  end
  assign VROW_y_mux_1_nl = MUX_v_9_2_2(VROW_y_sva, VROW_y_sva_mx0w2, fsm_output[2]);
  assign VCOL_not_8_nl = ~ or_tmp_69;
  assign VROW_y_not_2_nl = ~ or_tmp_69;
  assign not_281_nl = ~ and_133_cse;
  assign nand_17_nl = ~(VCOL_stage_0_1 & (~ mux_tmp_54));
  assign mux_55_nl = MUX_s_1_2_2(and_tmp_16, nand_17_nl, VCOL_stage_v);
  assign nl_dy_chan_rsci_idat_35_27  = ({1'b1 , (pix2_pix_lpi_3_dfm_1[31:24])}) +
      conv_u2s_8_9(~ (pix0_pix_lpi_3_dfm_2_mx1[31:24])) + 9'b000000001;
  assign nl_dy_chan_rsci_idat_8_0  = ({1'b1 , (pix2_pix_lpi_3_dfm_1[7:0])}) + conv_u2s_8_9(~
      (pix0_pix_lpi_3_dfm_2_mx1[7:0])) + 9'b000000001;
  assign nl_dy_chan_rsci_idat_26_18  = ({1'b1 , (pix2_pix_lpi_3_dfm_1[23:16])}) +
      conv_u2s_8_9(~ (pix0_pix_lpi_3_dfm_2_mx1[23:16])) + 9'b000000001;
  assign nl_dy_chan_rsci_idat_17_9  = ({1'b1 , (pix2_pix_lpi_3_dfm_1[15:8])}) + conv_u2s_8_9(~
      (pix0_pix_lpi_3_dfm_2_mx1[15:8])) + 9'b000000001;
  assign or_98_nl = VCOL_equal_1_tmp | or_dcpl_25;
  assign mux_79_nl = MUX_s_1_2_2(or_98_nl, mux_tmp_54, and_268_cse);
  assign rdbuf1_pix_and_1_nl = (~ (VCOL_x_sva[0])) & VCOL_stage_v_1;
  assign pix0_pix_pix0_pix_nor_nl = ~(pix0_pix_lpi_3_mx1c1 | and_133_cse);
  assign pix0_pix_and_3_nl = pix0_pix_lpi_3_mx1c1 & (~ and_133_cse);
  assign and_119_nl = VCOL_stage_0_2 & (~ VROW_equal_tmp);

  function automatic [31:0] MUX1HOT_v_32_3_2;
    input [31:0] input_2;
    input [31:0] input_1;
    input [31:0] input_0;
    input [2:0] sel;
    reg [31:0] result;
  begin
    result = input_0 & {32{sel[0]}};
    result = result | (input_1 & {32{sel[1]}});
    result = result | (input_2 & {32{sel[2]}});
    MUX1HOT_v_32_3_2 = result;
  end
  endfunction


  function automatic [63:0] MUX1HOT_v_64_3_2;
    input [63:0] input_2;
    input [63:0] input_1;
    input [63:0] input_0;
    input [2:0] sel;
    reg [63:0] result;
  begin
    result = input_0 & {64{sel[0]}};
    result = result | (input_1 & {64{sel[1]}});
    result = result | (input_2 & {64{sel[2]}});
    MUX1HOT_v_64_3_2 = result;
  end
  endfunction


  function automatic  MUX_s_1_2_2;
    input  input_0;
    input  input_1;
    input  sel;
    reg  result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_s_1_2_2 = result;
  end
  endfunction


  function automatic [9:0] MUX_v_10_2_2;
    input [9:0] input_0;
    input [9:0] input_1;
    input  sel;
    reg [9:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_10_2_2 = result;
  end
  endfunction


  function automatic [31:0] MUX_v_32_2_2;
    input [31:0] input_0;
    input [31:0] input_1;
    input  sel;
    reg [31:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_32_2_2 = result;
  end
  endfunction


  function automatic [6:0] MUX_v_7_2_2;
    input [6:0] input_0;
    input [6:0] input_1;
    input  sel;
    reg [6:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_7_2_2 = result;
  end
  endfunction


  function automatic [8:0] MUX_v_9_2_2;
    input [8:0] input_0;
    input [8:0] input_1;
    input  sel;
    reg [8:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_9_2_2 = result;
  end
  endfunction


  function automatic [0:0] readslicef_10_1_9;
    input [9:0] vector;
    reg [9:0] tmp;
  begin
    tmp = vector >> 9;
    readslicef_10_1_9 = tmp[0:0];
  end
  endfunction


  function automatic [9:0] signext_10_9;
    input [8:0] vector;
  begin
    signext_10_9= {{1{vector[8]}}, vector};
  end
  endfunction


  function automatic [8:0] conv_u2s_8_9 ;
    input [7:0]  vector ;
  begin
    conv_u2s_8_9 =  {1'b0, vector};
  end
  endfunction


  function automatic [9:0] conv_u2s_9_10 ;
    input [8:0]  vector ;
  begin
    conv_u2s_9_10 =  {1'b0, vector};
  end
  endfunction

endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_HorDer_run
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_HorDer_run (
  clk, rst, arst_n, pix_chan1_rsc_dat, pix_chan1_rsc_vld, pix_chan1_rsc_rdy, widthIn,
      heightIn, pix_chan2_rsc_dat, pix_chan2_rsc_vld, pix_chan2_rsc_rdy, dx_chan_rsc_dat,
      dx_chan_rsc_vld, dx_chan_rsc_rdy
);
  input clk;
  input rst;
  input arst_n;
  input [31:0] pix_chan1_rsc_dat;
  input pix_chan1_rsc_vld;
  output pix_chan1_rsc_rdy;
  input [9:0] widthIn;
  input [8:0] heightIn;
  output [31:0] pix_chan2_rsc_dat;
  output pix_chan2_rsc_vld;
  input pix_chan2_rsc_rdy;
  output [35:0] dx_chan_rsc_dat;
  output dx_chan_rsc_vld;
  input dx_chan_rsc_rdy;


  // Interconnect Declarations
  wire run_wen;
  wire pix_chan1_rsci_wen_comp;
  wire [31:0] pix_chan1_rsci_idat_mxwt;
  wire pix_chan2_rsci_wen_comp;
  reg [31:0] pix_chan2_rsci_idat;
  wire dx_chan_rsci_wen_comp;
  reg [8:0] dx_chan_rsci_idat_35_27;
  wire [9:0] nl_dx_chan_rsci_idat_35_27;
  reg [8:0] dx_chan_rsci_idat_26_18;
  reg [8:0] dx_chan_rsci_idat_17_9;
  wire [5:0] fsm_output;
  wire HCOL_if_4_equal_tmp;
  wire or_dcpl_5;
  wire and_dcpl_1;
  wire and_dcpl_2;
  reg [9:0] HCOL_x_sva;
  reg [9:0] HCOL_acc_9_itm;
  wire [10:0] nl_HCOL_acc_9_itm;
  reg HCOL_if_slc_operator_11_true_acc_10_svs;
  reg reg_pix_chan2_rsci_oswt_cse;
  wire HCOL_if_3_and_1_cse;
  reg reg_dx_chan_rsci_iswt0_cse;
  reg reg_pix_chan1_rsci_iswt0_cse;
  wire [8:0] operator_8_false_11_acc_1_sdt;
  wire [9:0] nl_operator_8_false_11_acc_1_sdt;
  reg reg_dx_chan_rsci_idat_8_0_ftd;
  reg [7:0] reg_dx_chan_rsci_idat_8_0_ftd_1;
  wire nor_14_cse;
  wire HROW_y_or_cse;
  reg [8:0] HROW_y_sva;
  reg [31:0] pix0_lpi_3;
  reg [7:0] pix_buf0_31_24_lpi_3;
  reg [8:0] operator_8_false_5_acc_1_itm;
  wire [9:0] nl_operator_8_false_5_acc_1_itm;
  reg [8:0] operator_8_false_8_acc_1_itm;
  wire [9:0] nl_operator_8_false_8_acc_1_itm;
  reg operator_8_false_11_acc_1_itm_8;
  reg [7:0] operator_8_false_11_acc_1_itm_7_0;
  wire operator_11_true_acc_itm_10_1;

  wire pix0_not_1_nl;
  wire HCOL_x_not_2_nl;
  wire[7:0] pix0_mux_1_nl;
  wire[8:0] HROW_acc_nl;
  wire[9:0] nl_HROW_acc_nl;
  wire HROW_y_not_1_nl;
  wire[7:0] HCOL_mux_1_nl;
  wire HCOL_HCOL_nand_nl;
  wire[10:0] operator_11_true_acc_nl;
  wire[11:0] nl_operator_11_true_acc_nl;

  // Interconnect Declarations for Component Instantiations 
  wire [35:0] nl_EdgeDetect_IP_EdgeDetect_HorDer_run_dx_chan_rsci_inst_dx_chan_rsci_idat;
  assign nl_EdgeDetect_IP_EdgeDetect_HorDer_run_dx_chan_rsci_inst_dx_chan_rsci_idat
      = {dx_chan_rsci_idat_35_27 , dx_chan_rsci_idat_26_18 , dx_chan_rsci_idat_17_9
      , reg_dx_chan_rsci_idat_8_0_ftd , reg_dx_chan_rsci_idat_8_0_ftd_1};
  wire[8:0] operator_9_false_acc_nl;
  wire[9:0] nl_operator_9_false_acc_nl;
  wire  nl_EdgeDetect_IP_EdgeDetect_HorDer_run_run_fsm_inst_HROW_C_0_tr0;
  assign nl_operator_9_false_acc_nl = heightIn + 9'b111111111;
  assign operator_9_false_acc_nl = nl_operator_9_false_acc_nl[8:0];
  assign nl_EdgeDetect_IP_EdgeDetect_HorDer_run_run_fsm_inst_HROW_C_0_tr0 = HROW_y_sva
      == operator_9_false_acc_nl;
  EdgeDetect_IP_EdgeDetect_HorDer_run_pix_chan1_rsci EdgeDetect_IP_EdgeDetect_HorDer_run_pix_chan1_rsci_inst
      (
      .pix_chan1_rsc_dat(pix_chan1_rsc_dat),
      .pix_chan1_rsc_vld(pix_chan1_rsc_vld),
      .pix_chan1_rsc_rdy(pix_chan1_rsc_rdy),
      .pix_chan1_rsci_oswt(reg_pix_chan1_rsci_iswt0_cse),
      .pix_chan1_rsci_wen_comp(pix_chan1_rsci_wen_comp),
      .pix_chan1_rsci_idat_mxwt(pix_chan1_rsci_idat_mxwt)
    );
  EdgeDetect_IP_EdgeDetect_HorDer_run_pix_chan2_rsci EdgeDetect_IP_EdgeDetect_HorDer_run_pix_chan2_rsci_inst
      (
      .pix_chan2_rsc_dat(pix_chan2_rsc_dat),
      .pix_chan2_rsc_vld(pix_chan2_rsc_vld),
      .pix_chan2_rsc_rdy(pix_chan2_rsc_rdy),
      .pix_chan2_rsci_oswt(reg_pix_chan2_rsci_oswt_cse),
      .pix_chan2_rsci_wen_comp(pix_chan2_rsci_wen_comp),
      .pix_chan2_rsci_idat(pix_chan2_rsci_idat)
    );
  EdgeDetect_IP_EdgeDetect_HorDer_run_dx_chan_rsci EdgeDetect_IP_EdgeDetect_HorDer_run_dx_chan_rsci_inst
      (
      .dx_chan_rsc_dat(dx_chan_rsc_dat),
      .dx_chan_rsc_vld(dx_chan_rsc_vld),
      .dx_chan_rsc_rdy(dx_chan_rsc_rdy),
      .dx_chan_rsci_oswt(reg_dx_chan_rsci_iswt0_cse),
      .dx_chan_rsci_wen_comp(dx_chan_rsci_wen_comp),
      .dx_chan_rsci_idat(nl_EdgeDetect_IP_EdgeDetect_HorDer_run_dx_chan_rsci_inst_dx_chan_rsci_idat[35:0])
    );
  EdgeDetect_IP_EdgeDetect_HorDer_run_staller EdgeDetect_IP_EdgeDetect_HorDer_run_staller_inst
      (
      .run_wen(run_wen),
      .pix_chan1_rsci_wen_comp(pix_chan1_rsci_wen_comp),
      .pix_chan2_rsci_wen_comp(pix_chan2_rsci_wen_comp),
      .dx_chan_rsci_wen_comp(dx_chan_rsci_wen_comp)
    );
  EdgeDetect_IP_EdgeDetect_HorDer_run_run_fsm EdgeDetect_IP_EdgeDetect_HorDer_run_run_fsm_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .run_wen(run_wen),
      .fsm_output(fsm_output),
      .HCOL_C_2_tr0(and_dcpl_2),
      .HROW_C_0_tr0(nl_EdgeDetect_IP_EdgeDetect_HorDer_run_run_fsm_inst_HROW_C_0_tr0)
    );
  assign nor_14_cse = ~((HCOL_x_sva == widthIn) | HCOL_if_slc_operator_11_true_acc_10_svs);
  assign HCOL_if_3_and_1_cse = run_wen & (fsm_output[2]) & (~(and_dcpl_1 & (HCOL_x_sva[7:0]==8'b00000000)));
  assign HROW_y_or_cse = (fsm_output[4]) | (fsm_output[0]);
  assign HCOL_HCOL_nand_nl = ~((HCOL_x_sva==10'b0000000001));
  assign HCOL_mux_1_nl = MUX_v_8_2_2((pix0_lpi_3[31:24]), operator_8_false_11_acc_1_itm_7_0,
      HCOL_HCOL_nand_nl);
  assign nl_operator_8_false_11_acc_1_sdt = ({1'b1 , (pix0_lpi_3[15:8])}) + conv_u2s_8_9(~
      HCOL_mux_1_nl) + 9'b000000001;
  assign operator_8_false_11_acc_1_sdt = nl_operator_8_false_11_acc_1_sdt[8:0];
  assign nl_operator_11_true_acc_nl = ({3'b100 , (widthIn[9:2])}) + conv_u2s_10_11(~
      HCOL_x_sva);
  assign operator_11_true_acc_nl = nl_operator_11_true_acc_nl[10:0];
  assign operator_11_true_acc_itm_10_1 = readslicef_11_1_10(operator_11_true_acc_nl);
  assign HCOL_if_4_equal_tmp = (HCOL_x_sva[7:0]) == (widthIn[9:2]);
  assign or_dcpl_5 = (HCOL_x_sva[9:8]!=2'b00);
  assign and_dcpl_1 = ~((HCOL_x_sva[9:8]!=2'b00));
  assign and_dcpl_2 = and_dcpl_1 & HCOL_if_4_equal_tmp;
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      reg_pix_chan2_rsci_oswt_cse <= 1'b0;
      reg_dx_chan_rsci_iswt0_cse <= 1'b0;
      reg_pix_chan1_rsci_iswt0_cse <= 1'b0;
      operator_8_false_11_acc_1_itm_8 <= 1'b0;
      operator_8_false_11_acc_1_itm_7_0 <= 8'b00000000;
      operator_8_false_8_acc_1_itm <= 9'b000000000;
      operator_8_false_5_acc_1_itm <= 9'b000000000;
      HCOL_if_slc_operator_11_true_acc_10_svs <= 1'b0;
    end
    else if ( rst ) begin
      reg_pix_chan2_rsci_oswt_cse <= 1'b0;
      reg_dx_chan_rsci_iswt0_cse <= 1'b0;
      reg_pix_chan1_rsci_iswt0_cse <= 1'b0;
      operator_8_false_11_acc_1_itm_8 <= 1'b0;
      operator_8_false_11_acc_1_itm_7_0 <= 8'b00000000;
      operator_8_false_8_acc_1_itm <= 9'b000000000;
      operator_8_false_5_acc_1_itm <= 9'b000000000;
      HCOL_if_slc_operator_11_true_acc_10_svs <= 1'b0;
    end
    else if ( run_wen ) begin
      reg_pix_chan2_rsci_oswt_cse <= ((HCOL_acc_9_itm!=10'b0000000000)) & (or_dcpl_5
          | (~ HCOL_if_4_equal_tmp)) & (fsm_output[3]);
      reg_dx_chan_rsci_iswt0_cse <= (or_dcpl_5 | (HCOL_x_sva[7:0]!=8'b00000000))
          & (fsm_output[2]);
      reg_pix_chan1_rsci_iswt0_cse <= (~ operator_11_true_acc_itm_10_1) & (fsm_output[1]);
      operator_8_false_11_acc_1_itm_8 <= operator_8_false_11_acc_1_sdt[8];
      operator_8_false_11_acc_1_itm_7_0 <= MUX_v_8_2_2((operator_8_false_11_acc_1_sdt[7:0]),
          pix_buf0_31_24_lpi_3, fsm_output[3]);
      operator_8_false_8_acc_1_itm <= nl_operator_8_false_8_acc_1_itm[8:0];
      operator_8_false_5_acc_1_itm <= nl_operator_8_false_5_acc_1_itm[8:0];
      HCOL_if_slc_operator_11_true_acc_10_svs <= operator_11_true_acc_itm_10_1;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_chan2_rsci_idat <= 32'b00000000000000000000000000000000;
    end
    else if ( rst ) begin
      pix_chan2_rsci_idat <= 32'b00000000000000000000000000000000;
    end
    else if ( run_wen & (~(((HCOL_acc_9_itm==10'b0000000000)) | and_dcpl_2 | (~ (fsm_output[3]))))
        ) begin
      pix_chan2_rsci_idat <= pix0_lpi_3;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix0_lpi_3 <= 32'b00000000000000000000000000000000;
    end
    else if ( rst ) begin
      pix0_lpi_3 <= 32'b00000000000000000000000000000000;
    end
    else if ( run_wen & (((fsm_output[2]) & nor_14_cse) | (fsm_output[0])) ) begin
      pix0_lpi_3 <= MUX_v_32_2_2(32'b00000000000000000000000000000000, pix_chan1_rsci_idat_mxwt,
          pix0_not_1_nl);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      HCOL_x_sva <= 10'b0000000000;
    end
    else if ( rst ) begin
      HCOL_x_sva <= 10'b0000000000;
    end
    else if ( run_wen & ((fsm_output[3]) | HROW_y_or_cse) ) begin
      HCOL_x_sva <= MUX_v_10_2_2(10'b0000000000, HCOL_acc_9_itm, HCOL_x_not_2_nl);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      dx_chan_rsci_idat_35_27 <= 9'b000000000;
      reg_dx_chan_rsci_idat_8_0_ftd <= 1'b0;
      reg_dx_chan_rsci_idat_8_0_ftd_1 <= 8'b00000000;
      dx_chan_rsci_idat_26_18 <= 9'b000000000;
      dx_chan_rsci_idat_17_9 <= 9'b000000000;
    end
    else if ( rst ) begin
      dx_chan_rsci_idat_35_27 <= 9'b000000000;
      reg_dx_chan_rsci_idat_8_0_ftd <= 1'b0;
      reg_dx_chan_rsci_idat_8_0_ftd_1 <= 8'b00000000;
      dx_chan_rsci_idat_26_18 <= 9'b000000000;
      dx_chan_rsci_idat_17_9 <= 9'b000000000;
    end
    else if ( HCOL_if_3_and_1_cse ) begin
      dx_chan_rsci_idat_35_27 <= nl_dx_chan_rsci_idat_35_27[8:0];
      reg_dx_chan_rsci_idat_8_0_ftd <= operator_8_false_11_acc_1_itm_8;
      reg_dx_chan_rsci_idat_8_0_ftd_1 <= operator_8_false_11_acc_1_itm_7_0;
      dx_chan_rsci_idat_26_18 <= operator_8_false_5_acc_1_itm;
      dx_chan_rsci_idat_17_9 <= operator_8_false_8_acc_1_itm;
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      HROW_y_sva <= 9'b000000000;
    end
    else if ( rst ) begin
      HROW_y_sva <= 9'b000000000;
    end
    else if ( run_wen & HROW_y_or_cse ) begin
      HROW_y_sva <= MUX_v_9_2_2(9'b000000000, HROW_acc_nl, HROW_y_not_1_nl);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      pix_buf0_31_24_lpi_3 <= 8'b00000000;
    end
    else if ( rst ) begin
      pix_buf0_31_24_lpi_3 <= 8'b00000000;
    end
    else if ( run_wen & ((fsm_output[3]) | (fsm_output[4]) | (fsm_output[0])) ) begin
      pix_buf0_31_24_lpi_3 <= pix0_lpi_3[31:24];
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      HCOL_acc_9_itm <= 10'b0000000000;
    end
    else if ( rst ) begin
      HCOL_acc_9_itm <= 10'b0000000000;
    end
    else if ( run_wen & (fsm_output[1]) ) begin
      HCOL_acc_9_itm <= nl_HCOL_acc_9_itm[9:0];
    end
  end
  assign nl_operator_8_false_8_acc_1_itm  = ({1'b1 , (~ (pix0_lpi_3[7:0]))}) + conv_u2s_8_9(pix0_lpi_3[23:16])
      + 9'b000000001;
  assign nl_operator_8_false_5_acc_1_itm  = ({1'b1 , (~ (pix0_lpi_3[15:8]))}) + conv_u2s_8_9(pix0_lpi_3[31:24])
      + 9'b000000001;
  assign pix0_not_1_nl = ~ (fsm_output[0]);
  assign HCOL_x_not_2_nl = ~ HROW_y_or_cse;
  assign pix0_mux_1_nl = MUX_v_8_2_2((pix0_lpi_3[7:0]), (pix_chan1_rsci_idat_mxwt[7:0]),
      nor_14_cse);
  assign nl_dx_chan_rsci_idat_35_27  = ({1'b1 , pix0_mux_1_nl}) + conv_u2s_8_9(~
      (pix0_lpi_3[23:16])) + 9'b000000001;
  assign nl_HROW_acc_nl = HROW_y_sva + 9'b000000001;
  assign HROW_acc_nl = nl_HROW_acc_nl[8:0];
  assign HROW_y_not_1_nl = ~ (fsm_output[0]);
  assign nl_HCOL_acc_9_itm  = HCOL_x_sva + 10'b0000000001;

  function automatic [9:0] MUX_v_10_2_2;
    input [9:0] input_0;
    input [9:0] input_1;
    input  sel;
    reg [9:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_10_2_2 = result;
  end
  endfunction


  function automatic [31:0] MUX_v_32_2_2;
    input [31:0] input_0;
    input [31:0] input_1;
    input  sel;
    reg [31:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_32_2_2 = result;
  end
  endfunction


  function automatic [7:0] MUX_v_8_2_2;
    input [7:0] input_0;
    input [7:0] input_1;
    input  sel;
    reg [7:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_8_2_2 = result;
  end
  endfunction


  function automatic [8:0] MUX_v_9_2_2;
    input [8:0] input_0;
    input [8:0] input_1;
    input  sel;
    reg [8:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_9_2_2 = result;
  end
  endfunction


  function automatic [0:0] readslicef_11_1_10;
    input [10:0] vector;
    reg [10:0] tmp;
  begin
    tmp = vector >> 10;
    readslicef_11_1_10 = tmp[0:0];
  end
  endfunction


  function automatic [8:0] conv_u2s_8_9 ;
    input [7:0]  vector ;
  begin
    conv_u2s_8_9 =  {1'b0, vector};
  end
  endfunction


  function automatic [10:0] conv_u2s_10_11 ;
    input [9:0]  vector ;
  begin
    conv_u2s_10_11 =  {1'b0, vector};
  end
  endfunction

endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng_run
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng_run (
  clk, rst, arst_n, dx_chan_rsc_dat, dx_chan_rsc_vld, dx_chan_rsc_rdy, dy_chan_rsc_dat,
      dy_chan_rsc_vld, dy_chan_rsc_rdy, pix_chan2_rsc_dat, pix_chan2_rsc_vld, pix_chan2_rsc_rdy,
      widthIn, heightIn, sw_in_triosy_lz, crc32_pix_in_rsc_zout, crc32_pix_in_rsc_lzout,
      crc32_pix_in_rsc_zin, crc32_pix_in_triosy_lz, crc32_dat_out_rsc_zout, crc32_dat_out_rsc_lzout,
      crc32_dat_out_rsc_zin, crc32_dat_out_triosy_lz, dat_out_rsc_dat, dat_out_rsc_vld,
      dat_out_rsc_rdy, sw_in_rsci_idat
);
  input clk;
  input rst;
  input arst_n;
  input [35:0] dx_chan_rsc_dat;
  input dx_chan_rsc_vld;
  output dx_chan_rsc_rdy;
  input [35:0] dy_chan_rsc_dat;
  input dy_chan_rsc_vld;
  output dy_chan_rsc_rdy;
  input [31:0] pix_chan2_rsc_dat;
  input pix_chan2_rsc_vld;
  output pix_chan2_rsc_rdy;
  input [9:0] widthIn;
  input [8:0] heightIn;
  output sw_in_triosy_lz;
  output [31:0] crc32_pix_in_rsc_zout;
  output crc32_pix_in_rsc_lzout;
  input [31:0] crc32_pix_in_rsc_zin;
  output crc32_pix_in_triosy_lz;
  output [31:0] crc32_dat_out_rsc_zout;
  output crc32_dat_out_rsc_lzout;
  input [31:0] crc32_dat_out_rsc_zin;
  output crc32_dat_out_triosy_lz;
  output [33:0] dat_out_rsc_dat;
  output dat_out_rsc_vld;
  input dat_out_rsc_rdy;
  input sw_in_rsci_idat;


  // Interconnect Declarations
  wire run_wen;
  wire run_wten;
  wire dx_chan_rsci_wen_comp;
  wire [35:0] dx_chan_rsci_idat_mxwt;
  wire dy_chan_rsci_wen_comp;
  wire [35:0] dy_chan_rsci_idat_mxwt;
  wire pix_chan2_rsci_wen_comp;
  wire [31:0] pix_chan2_rsci_idat_mxwt;
  wire [31:0] crc32_pix_in_rsci_din;
  wire [31:0] crc32_dat_out_rsci_din;
  wire dat_out_rsci_wen_comp;
  reg dat_out_rsci_idat_33;
  reg dat_out_rsci_idat_32;
  reg [7:0] dat_out_rsci_idat_31_24;
  reg [7:0] dat_out_rsci_idat_23_16;
  reg [7:0] dat_out_rsci_idat_15_8;
  reg [7:0] dat_out_rsci_idat_7_0;
  wire [6:0] fsm_output;
  wire MROW_equal_tmp;
  wire MCOL_equal_2_tmp;
  wire or_tmp_1;
  wire or_tmp_2;
  wire or_tmp_15;
  wire and_484_cse;
  wire [8:0] abs_sum_1_sva_1;
  wire [9:0] nl_abs_sum_1_sva_1;
  wire [8:0] abs_sum_2_sva_1;
  wire [9:0] nl_abs_sum_2_sva_1;
  wire [8:0] abs_sum_3_sva_1;
  wire [9:0] nl_abs_sum_3_sva_1;
  wire [8:0] abs_sum_0_sva_1;
  wire [9:0] nl_abs_sum_0_sva_1;
  wire MCOL_and_cse;
  wire MCOL_and_4_cse;
  reg reg_crc32_dat_out_triosy_obj_iswt0_cse;
  reg reg_dat_out_rsci_iswt0_cse;
  reg reg_pix_chan2_rsci_iswt0_cse;
  wire MROW_y_or_cse;
  wire or_244_rmff;
  wire xor_cse_320;
  wire xor_cse_156;
  wire xor_cse_75;
  wire xor_cse_334;
  wire xor_cse_353;
  wire xor_cse_321;
  wire xor_cse_337;
  wire xor_cse_358;
  wire xor_cse_23;
  wire xor_cse_410;
  wire xor_cse_331;
  wire xor_cse_294;
  wire xor_cse_326;
  wire xor_cse_131;
  wire xor_cse_293;
  wire xor_cse_109;
  wire xor_cse_379;
  wire xor_cse_296;
  wire xor_cse_324;
  wire xor_cse_120;
  wire xor_cse_316;
  wire xor_cse_253;
  wire xor_cse_328;
  wire xor_cse_367;
  wire xor_cse_309;
  wire xor_cse_349;
  wire xor_cse_308;
  wire xor_cse_360;
  wire xor_cse_267;
  wire xor_cse_259;
  wire xor_cse_312;
  wire xor_cse_327;
  wire xor_cse_361;
  wire xor_cse_329;
  wire xor_cse_295;
  wire xor_cse_372;
  wire xor_cse_343;
  wire xor_cse_381;
  wire xor_cse_57;
  wire xor_cse_338;
  wire xor_cse_302;
  wire xor_cse_341;
  wire xor_cse_323;
  wire xor_cse_373;
  wire xor_cse_345;
  wire xor_cse_355;
  wire xor_cse_317;
  wire xor_cse_215;
  wire xor_cse_352;
  wire xor_cse_94;
  wire xor_cse_359;
  wire xor_cse_347;
  wire xor_cse_292;
  wire xor_cse_195;
  wire xor_cse_318;
  wire xor_cse_187;
  wire xor_cse_38;
  wire xor_cse_297;
  wire xor_cse_305;
  wire xor_cse_313;
  wire xor_cse_123;
  wire xor_cse_108;
  wire xor_cse_300;
  wire xor_cse_301;
  wire xor_cse_148;
  wire xor_cse_47;
  wire xor_cse_1;
  wire xor_cse_150;
  wire xor_cse_264;
  wire [7:0] MCOL_qr_10_lpi_3_dfm_1;
  wire [7:0] MCOL_qr_8_lpi_3_dfm_1;
  wire xor_cse_74;
  wire xor_cse_170;
  wire xor_cse_133;
  wire xor_cse_48;
  wire xor_cse_126;
  wire xor_cse_211;
  wire [7:0] MCOL_qr_11_lpi_3_dfm_1;
  wire xor_cse_154;
  wire xor_cse_144;
  wire xor_cse_216;
  wire xor_cse_125;
  wire xor_cse_136;
  wire xor_cse_164;
  wire xor_cse_32;
  wire xor_cse_179;
  wire xor_cse_121;
  wire xor_cse_225;
  wire xor_cse_135;
  wire xor_cse_100;
  wire xor_cse_127;
  wire xor_cse_256;
  wire xor_cse_51;
  wire xor_cse_221;
  wire xor_cse_205;
  wire xor_cse_169;
  wire xor_cse_40;
  wire xor_cse_84;
  wire xor_cse_114;
  wire xor_cse_88;
  wire xor_cse_102;
  wire xor_cse_71;
  wire xor_cse_234;
  wire [7:0] MCOL_qr_9_lpi_3_dfm_1;
  wire xor_cse_168;
  wire xor_cse_81;
  wire xor_cse_83;
  wire xor_cse_172;
  wire xor_cse_89;
  wire xor_cse_93;
  wire xor_cse_223;
  wire xor_cse_142;
  wire xor_cse_254;
  wire xor_cse_68;
  wire xor_cse_192;
  wire xor_cse_248;
  wire xor_cse_77;
  wire xor_cse_98;
  wire xor_cse_78;
  wire xor_cse_79;
  wire xor_cse_85;
  wire xor_cse_101;
  wire xor_cse_137;
  wire xor_cse_240;
  wire xor_cse_206;
  wire xor_cse_45;
  wire xor_cse_163;
  wire xor_cse_222;
  wire xor_cse_9;
  wire xor_cse_159;
  wire xor_cse_245;
  wire xor_cse_201;
  wire xor_cse_161;
  wire xor_cse_146;
  wire xor_cse_8;
  wire xor_cse_219;
  wire xor_cse_202;
  wire xor_cse_132;
  wire xor_cse_39;
  wire xor_cse_189;
  wire xor_cse_182;
  wire xor_cse_193;
  wire xor_cse_140;
  wire xor_cse_185;
  wire xor_cse_26;
  wire xor_cse_63;
  wire xor_cse_115;
  wire xor_cse_183;
  wire xor_cse_174;
  wire xor_cse_97;
  wire xor_cse_112;
  wire xor_cse;
  wire xor_cse_29;
  wire xor_cse_42;
  wire xor_cse_103;
  wire xor_cse_24;
  wire xor_cse_178;
  wire xor_cse_65;
  wire xor_cse_69;
  wire xor_cse_58;
  wire xor_cse_60;
  wire xor_cse_152;
  wire xor_cse_59;
  wire xor_cse_4;
  wire xor_cse_149;
  wire xor_cse_99;
  wire xor_cse_117;
  wire xor_cse_122;
  wire xor_cse_44;
  wire xor_cse_20;
  reg [8:0] MROW_y_sva;
  reg [9:0] MCOL_x_sva;
  reg [9:0] MCOL_acc_4_itm;
  wire [10:0] nl_MCOL_acc_4_itm;

  wire[7:0] operator_10_false_acc_nl;
  wire[8:0] nl_operator_10_false_acc_nl;
  wire[8:0] MROW_acc_nl;
  wire[9:0] nl_MROW_acc_nl;
  wire MROW_y_not_1_nl;
  wire MCOL_x_not_1_nl;
  wire[7:0] MCOL_mux_2_nl;
  wire[7:0] MCOL_qif_2_acc_nl;
  wire[8:0] nl_MCOL_qif_2_acc_nl;
  wire[7:0] MCOL_mux_3_nl;
  wire[7:0] MCOL_qif_3_acc_nl;
  wire[8:0] nl_MCOL_qif_3_acc_nl;
  wire[7:0] MCOL_mux_4_nl;
  wire[7:0] MCOL_qif_4_acc_nl;
  wire[8:0] nl_MCOL_qif_4_acc_nl;
  wire[7:0] MCOL_mux_5_nl;
  wire[7:0] MCOL_qif_5_acc_nl;
  wire[8:0] nl_MCOL_qif_5_acc_nl;
  wire[7:0] MCOL_mux_6_nl;
  wire[7:0] MCOL_qif_6_acc_nl;
  wire[8:0] nl_MCOL_qif_6_acc_nl;
  wire[7:0] MCOL_mux_7_nl;
  wire[7:0] MCOL_qif_7_acc_nl;
  wire[8:0] nl_MCOL_qif_7_acc_nl;
  wire[7:0] MCOL_mux_8_nl;
  wire[7:0] MCOL_qif_acc_nl;
  wire[8:0] nl_MCOL_qif_acc_nl;
  wire[7:0] MCOL_mux_9_nl;
  wire[7:0] MCOL_qif_1_acc_nl;
  wire[8:0] nl_MCOL_qif_1_acc_nl;
  wire[8:0] operator_9_false_acc_nl;
  wire[9:0] nl_operator_9_false_acc_nl;
  wire[8:0] operator_11_true_acc_nl;
  wire[9:0] nl_operator_11_true_acc_nl;

  // Interconnect Declarations for Component Instantiations 
  wire  nl_EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_rsci_inst_run_wten;
  assign nl_EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_rsci_inst_run_wten =
      ~ run_wen;
  wire EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_for_tmp_bit_EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_for_tmp_bit_or_nl;
  wire EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_for_tmp_bit_mux_nl;
  wire EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_for_tmp_bit_xor_nl;
  wire or_314_nl;
  wire mux_30_nl;
  wire xor_474_nl;
  wire or_313_nl;
  wire mux_29_nl;
  wire xor_471_nl;
  wire or_312_nl;
  wire mux_28_nl;
  wire xor_466_nl;
  wire or_311_nl;
  wire mux_27_nl;
  wire xor_463_nl;
  wire or_310_nl;
  wire mux_26_nl;
  wire xor_459_nl;
  wire or_309_nl;
  wire mux_25_nl;
  wire xor_454_nl;
  wire or_308_nl;
  wire mux_24_nl;
  wire xor_450_nl;
  wire or_307_nl;
  wire mux_23_nl;
  wire xor_446_nl;
  wire or_306_nl;
  wire mux_22_nl;
  wire xor_442_nl;
  wire or_305_nl;
  wire mux_21_nl;
  wire xor_440_nl;
  wire or_304_nl;
  wire mux_20_nl;
  wire xor_437_nl;
  wire or_303_nl;
  wire mux_19_nl;
  wire xor_432_nl;
  wire or_302_nl;
  wire mux_18_nl;
  wire xor_429_nl;
  wire or_301_nl;
  wire mux_17_nl;
  wire xor_426_nl;
  wire or_300_nl;
  wire mux_16_nl;
  wire xor_422_nl;
  wire or_299_nl;
  wire mux_15_nl;
  wire xor_417_nl;
  wire or_298_nl;
  wire mux_14_nl;
  wire xor_411_nl;
  wire or_297_nl;
  wire mux_13_nl;
  wire xor_407_nl;
  wire or_296_nl;
  wire mux_12_nl;
  wire xor_402_nl;
  wire or_295_nl;
  wire mux_11_nl;
  wire xor_396_nl;
  wire or_294_nl;
  wire mux_10_nl;
  wire xor_389_nl;
  wire or_293_nl;
  wire mux_9_nl;
  wire xor_386_nl;
  wire or_292_nl;
  wire mux_8_nl;
  wire xor_379_nl;
  wire or_291_nl;
  wire mux_7_nl;
  wire xor_373_nl;
  wire or_290_nl;
  wire mux_6_nl;
  wire xor_367_nl;
  wire or_289_nl;
  wire mux_5_nl;
  wire xor_361_nl;
  wire or_288_nl;
  wire mux_4_nl;
  wire xor_354_nl;
  wire or_287_nl;
  wire mux_3_nl;
  wire xor_349_nl;
  wire or_286_nl;
  wire mux_2_nl;
  wire xor_344_nl;
  wire or_285_nl;
  wire mux_1_nl;
  wire xor_336_nl;
  wire or_284_nl;
  wire mux_nl;
  wire xor_330_nl;
  wire [31:0] nl_EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_rsci_inst_crc32_pix_in_rsci_dout_run;
  assign EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_for_tmp_bit_xor_nl = xor_cse_320
      ^ (crc32_pix_in_rsci_din[2]) ^ (pix_chan2_rsci_idat_mxwt[2]) ^ (pix_chan2_rsci_idat_mxwt[21])
      ^ (pix_chan2_rsci_idat_mxwt[1]) ^ xor_cse_156 ^ xor_cse_75 ^ xor_cse_334 ^
      xor_cse_353;
  assign EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_for_tmp_bit_mux_nl = MUX_s_1_2_2(EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_for_tmp_bit_xor_nl,
      (~ (crc32_pix_in_rsci_din[31])), fsm_output[5]);
  assign EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_for_tmp_bit_EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_for_tmp_bit_or_nl
      = EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_for_tmp_bit_mux_nl | or_tmp_15;
  assign xor_474_nl = xor_cse_321 ^ xor_cse_337 ^ xor_cse_358 ^ xor_cse_23 ^ xor_cse_410
      ^ (crc32_pix_in_rsci_din[20]) ^ (crc32_pix_in_rsci_din[3]) ^ (crc32_pix_in_rsci_din[22])
      ^ (crc32_pix_in_rsci_din[19]) ^ (pix_chan2_rsci_idat_mxwt[19]) ^ (pix_chan2_rsci_idat_mxwt[31]);
  assign mux_30_nl = MUX_s_1_2_2(xor_474_nl, (~ (crc32_pix_in_rsci_din[30])), fsm_output[5]);
  assign or_314_nl = mux_30_nl | or_tmp_15;
  assign xor_471_nl = xor_cse_331 ^ (crc32_pix_in_rsci_din[0]) ^ xor_cse_156 ^ xor_cse_321
      ^ xor_cse_294 ^ xor_cse_326 ^ xor_cse_410 ^ (crc32_pix_in_rsci_din[5]) ^ (pix_chan2_rsci_idat_mxwt[5])
      ^ (crc32_pix_in_rsci_din[22]) ^ (crc32_pix_in_rsci_din[15]);
  assign mux_29_nl = MUX_s_1_2_2(xor_471_nl, (~ (crc32_pix_in_rsci_din[29])), fsm_output[5]);
  assign or_313_nl = mux_29_nl | or_tmp_15;
  assign xor_466_nl = xor_cse_131 ^ xor_cse_293 ^ xor_cse_109 ^ xor_cse_379 ^ xor_cse_296
      ^ xor_cse_324 ^ (crc32_pix_in_rsci_din[29]) ^ (crc32_pix_in_rsci_din[23]) ^
      (crc32_pix_in_rsci_din[17]) ^ (pix_chan2_rsci_idat_mxwt[23]) ^ (crc32_pix_in_rsci_din[24])
      ^ (crc32_pix_in_rsci_din[14]) ^ (pix_chan2_rsci_idat_mxwt[14]);
  assign mux_28_nl = MUX_s_1_2_2(xor_466_nl, (~ (crc32_pix_in_rsci_din[28])), fsm_output[5]);
  assign or_312_nl = mux_28_nl | or_tmp_15;
  assign xor_463_nl = xor_cse_120 ^ xor_cse_109 ^ xor_cse_321 ^ xor_cse_316 ^ xor_cse_253
      ^ xor_cse_328 ^ (crc32_pix_in_rsci_din[16]) ^ (crc32_pix_in_rsci_din[29]) ^
      (crc32_pix_in_rsci_din[13]) ^ (pix_chan2_rsci_idat_mxwt[29]) ^ (pix_chan2_rsci_idat_mxwt[7])
      ^ (crc32_pix_in_rsci_din[6]) ^ (crc32_pix_in_rsci_din[1]) ^ (pix_chan2_rsci_idat_mxwt[1])
      ^ (crc32_pix_in_rsci_din[0]) ^ (crc32_pix_in_rsci_din[19]);
  assign mux_27_nl = MUX_s_1_2_2(xor_463_nl, (~ (crc32_pix_in_rsci_din[27])), fsm_output[5]);
  assign or_311_nl = mux_27_nl | or_tmp_15;
  assign xor_459_nl = xor_cse_367 ^ xor_cse_321 ^ xor_cse_316 ^ xor_cse_309 ^ xor_cse_379
      ^ (pix_chan2_rsci_idat_mxwt[12]) ^ (crc32_pix_in_rsci_din[24]) ^ (crc32_pix_in_rsci_din[18])
      ^ (pix_chan2_rsci_idat_mxwt[18]) ^ (pix_chan2_rsci_idat_mxwt[24]) ^ (pix_chan2_rsci_idat_mxwt[30])
      ^ (pix_chan2_rsci_idat_mxwt[2]) ^ (pix_chan2_rsci_idat_mxwt[31]);
  assign mux_26_nl = MUX_s_1_2_2(xor_459_nl, (~ (crc32_pix_in_rsci_din[26])), fsm_output[5]);
  assign or_310_nl = mux_26_nl | or_tmp_15;
  assign xor_454_nl = xor_cse_349 ^ (crc32_pix_in_rsci_din[20]) ^ xor_cse_131 ^ xor_cse_316
      ^ xor_cse_308 ^ xor_cse_360 ^ xor_cse_267 ^ (crc32_pix_in_rsci_din[26]) ^ (pix_chan2_rsci_idat_mxwt[26])
      ^ (crc32_pix_in_rsci_din[30]) ^ (pix_chan2_rsci_idat_mxwt[2]);
  assign mux_25_nl = MUX_s_1_2_2(xor_454_nl, (~ (crc32_pix_in_rsci_din[25])), fsm_output[5]);
  assign or_309_nl = mux_25_nl | or_tmp_15;
  assign xor_450_nl = xor_cse_259 ^ (crc32_pix_in_rsci_din[15]) ^ xor_cse_120 ^ xor_cse_308
      ^ xor_cse_312 ^ xor_cse_327 ^ xor_cse_361 ^ (crc32_pix_in_rsci_din[28]) ^ (crc32_pix_in_rsci_din[23])
      ^ (crc32_pix_in_rsci_din[31]) ^ (crc32_pix_in_rsci_din[2]);
  assign mux_24_nl = MUX_s_1_2_2(xor_450_nl, (~ (crc32_pix_in_rsci_din[24])), fsm_output[5]);
  assign or_308_nl = mux_24_nl | or_tmp_15;
  assign xor_446_nl = xor_cse_337 ^ xor_cse_309 ^ xor_cse_253 ^ xor_cse_329 ^ (crc32_pix_in_rsci_din[23])
      ^ (pix_chan2_rsci_idat_mxwt[23]) ^ (crc32_pix_in_rsci_din[8]) ^ (pix_chan2_rsci_idat_mxwt[8])
      ^ (crc32_pix_in_rsci_din[27]) ^ (crc32_pix_in_rsci_din[20]) ^ (crc32_pix_in_rsci_din[31])
      ^ (crc32_pix_in_rsci_din[21]) ^ (pix_chan2_rsci_idat_mxwt[21]) ^ (crc32_pix_in_rsci_din[19]);
  assign mux_23_nl = MUX_s_1_2_2(xor_446_nl, (~ (crc32_pix_in_rsci_din[23])), fsm_output[5]);
  assign or_307_nl = mux_23_nl | or_tmp_15;
  assign xor_442_nl = (pix_chan2_rsci_idat_mxwt[30]) ^ xor_cse_295 ^ xor_cse_312
      ^ xor_cse_372 ^ xor_cse_343 ^ xor_cse_381 ^ (crc32_pix_in_rsci_din[22]) ^ (pix_chan2_rsci_idat_mxwt[22])
      ^ (pix_chan2_rsci_idat_mxwt[7]) ^ (crc32_pix_in_rsci_din[30]);
  assign mux_22_nl = MUX_s_1_2_2(xor_442_nl, (~ (crc32_pix_in_rsci_din[22])), fsm_output[5]);
  assign or_306_nl = mux_22_nl | or_tmp_15;
  assign xor_440_nl = xor_cse_57 ^ xor_cse_312 ^ xor_cse_309 ^ xor_cse_338 ^ xor_cse_302
      ^ (crc32_pix_in_rsci_din[18]) ^ (crc32_pix_in_rsci_din[12]) ^ (pix_chan2_rsci_idat_mxwt[12])
      ^ (crc32_pix_in_rsci_din[22]) ^ (crc32_pix_in_rsci_din[0]) ^ (pix_chan2_rsci_idat_mxwt[31]);
  assign mux_21_nl = MUX_s_1_2_2(xor_440_nl, (~ (crc32_pix_in_rsci_din[21])), fsm_output[5]);
  assign or_305_nl = mux_21_nl | or_tmp_15;
  assign xor_437_nl = xor_cse_341 ^ xor_cse_75 ^ xor_cse_293 ^ xor_cse_337 ^ xor_cse_338
      ^ xor_cse_323 ^ (pix_chan2_rsci_idat_mxwt[27]) ^ (crc32_pix_in_rsci_din[28])
      ^ (crc32_pix_in_rsci_din[16]) ^ (pix_chan2_rsci_idat_mxwt[16]) ^ (pix_chan2_rsci_idat_mxwt[28])
      ^ (crc32_pix_in_rsci_din[7]) ^ (crc32_pix_in_rsci_din[3]);
  assign mux_20_nl = MUX_s_1_2_2(xor_437_nl, (~ (crc32_pix_in_rsci_din[20])), fsm_output[5]);
  assign or_304_nl = mux_20_nl | or_tmp_15;
  assign xor_432_nl = xor_cse_156 ^ xor_cse_293 ^ xor_cse_321 ^ xor_cse_337 ^ xor_cse_312
      ^ xor_cse_372 ^ xor_cse_373 ^ xor_cse_381 ^ (pix_chan2_rsci_idat_mxwt[10])
      ^ (crc32_pix_in_rsci_din[1]) ^ (pix_chan2_rsci_idat_mxwt[1]);
  assign mux_19_nl = MUX_s_1_2_2(xor_432_nl, (~ (crc32_pix_in_rsci_din[19])), fsm_output[5]);
  assign or_303_nl = mux_19_nl | or_tmp_15;
  assign xor_429_nl = (pix_chan2_rsci_idat_mxwt[18]) ^ xor_cse_131 ^ xor_cse_109
      ^ xor_cse_308 ^ xor_cse_309 ^ xor_cse_360 ^ xor_cse_379 ^ xor_cse_345 ^ (crc32_pix_in_rsci_din[26])
      ^ (pix_chan2_rsci_idat_mxwt[26]) ^ (crc32_pix_in_rsci_din[0]) ^ (crc32_pix_in_rsci_din[18]);
  assign mux_18_nl = MUX_s_1_2_2(xor_429_nl, (~ (crc32_pix_in_rsci_din[18])), fsm_output[5]);
  assign or_302_nl = mux_18_nl | or_tmp_15;
  assign xor_426_nl = xor_cse_355 ^ xor_cse_316 ^ xor_cse_317 ^ xor_cse_360 ^ xor_cse_215
      ^ xor_cse_352 ^ (crc32_pix_in_rsci_din[24]) ^ (crc32_pix_in_rsci_din[28]) ^
      (crc32_pix_in_rsci_din[16]);
  assign mux_17_nl = MUX_s_1_2_2(xor_426_nl, (~ (crc32_pix_in_rsci_din[17])), fsm_output[5]);
  assign or_301_nl = mux_17_nl | or_tmp_15;
  assign xor_422_nl = xor_cse_94 ^ xor_cse_294 ^ xor_cse_358 ^ xor_cse_372 ^ xor_cse_359
      ^ xor_cse_373 ^ (crc32_pix_in_rsci_din[24]) ^ (crc32_pix_in_rsci_din[26]) ^
      (crc32_pix_in_rsci_din[28]) ^ (crc32_pix_in_rsci_din[22]) ^ (pix_chan2_rsci_idat_mxwt[22])
      ^ (pix_chan2_rsci_idat_mxwt[28]);
  assign mux_16_nl = MUX_s_1_2_2(xor_422_nl, (~ (crc32_pix_in_rsci_din[16])), fsm_output[5]);
  assign or_300_nl = mux_16_nl | or_tmp_15;
  assign xor_417_nl = xor_cse_367 ^ xor_cse_294 ^ xor_cse_317 ^ xor_cse_347 ^ xor_cse_292
      ^ (crc32_pix_in_rsci_din[9]) ^ (pix_chan2_rsci_idat_mxwt[9]) ^ (crc32_pix_in_rsci_din[14])
      ^ (crc32_pix_in_rsci_din[27]) ^ (crc32_pix_in_rsci_din[31]) ^ (crc32_pix_in_rsci_din[19]);
  assign mux_15_nl = MUX_s_1_2_2(xor_417_nl, (~ (crc32_pix_in_rsci_din[15])), fsm_output[5]);
  assign or_299_nl = mux_15_nl | or_tmp_15;
  assign xor_411_nl = (pix_chan2_rsci_idat_mxwt[30]) ^ xor_cse_293 ^ xor_cse_195
      ^ xor_cse_318 ^ xor_cse_187 ^ (crc32_pix_in_rsci_din[11]) ^ (pix_chan2_rsci_idat_mxwt[11])
      ^ (crc32_pix_in_rsci_din[8]) ^ (crc32_pix_in_rsci_din[25]) ^ (crc32_pix_in_rsci_din[9])
      ^ (pix_chan2_rsci_idat_mxwt[9]) ^ (crc32_pix_in_rsci_din[13]) ^ (crc32_pix_in_rsci_din[17])
      ^ (pix_chan2_rsci_idat_mxwt[26]) ^ (crc32_pix_in_rsci_din[1]) ^ (pix_chan2_rsci_idat_mxwt[1])
      ^ (crc32_pix_in_rsci_din[18]);
  assign mux_14_nl = MUX_s_1_2_2(xor_411_nl, (~ (crc32_pix_in_rsci_din[14])), fsm_output[5]);
  assign or_298_nl = mux_14_nl | or_tmp_15;
  assign xor_407_nl = xor_cse_38 ^ xor_cse_317 ^ xor_cse_327 ^ xor_cse_360 ^ xor_cse_361
      ^ (crc32_pix_in_rsci_din[24]) ^ (pix_chan2_rsci_idat_mxwt[16]) ^ (crc32_pix_in_rsci_din[0])
      ^ (pix_chan2_rsci_idat_mxwt[0]) ^ (pix_chan2_rsci_idat_mxwt[17]) ^ (pix_chan2_rsci_idat_mxwt[29]);
  assign mux_13_nl = MUX_s_1_2_2(xor_407_nl, (~ (crc32_pix_in_rsci_din[13])), fsm_output[5]);
  assign or_297_nl = mux_13_nl | or_tmp_15;
  assign xor_402_nl = xor_cse_355 ^ (pix_chan2_rsci_idat_mxwt[6]) ^ (pix_chan2_rsci_idat_mxwt[7])
      ^ (crc32_pix_in_rsci_din[28]) ^ (crc32_pix_in_rsci_din[2]) ^ (crc32_pix_in_rsci_din[16])
      ^ xor_cse_308 ^ xor_cse_358 ^ xor_cse_359;
  assign mux_12_nl = MUX_s_1_2_2(xor_402_nl, (~ (crc32_pix_in_rsci_din[12])), fsm_output[5]);
  assign or_296_nl = mux_12_nl | or_tmp_15;
  assign xor_396_nl = xor_cse_349 ^ (crc32_pix_in_rsci_din[15]) ^ (pix_chan2_rsci_idat_mxwt[15])
      ^ xor_cse_75 ^ xor_cse_352 ^ xor_cse_353 ^ (pix_chan2_rsci_idat_mxwt[22]) ^
      (pix_chan2_rsci_idat_mxwt[14]) ^ (crc32_pix_in_rsci_din[27]) ^ (crc32_pix_in_rsci_din[3]);
  assign mux_11_nl = MUX_s_1_2_2(xor_396_nl, (~ (crc32_pix_in_rsci_din[11])), fsm_output[5]);
  assign or_295_nl = mux_11_nl | or_tmp_15;
  assign xor_389_nl = (pix_chan2_rsci_idat_mxwt[21]) ^ xor_cse_293 ^ xor_cse_57 ^
      xor_cse_326 ^ xor_cse_347 ^ xor_cse_297 ^ (crc32_pix_in_rsci_din[21]) ^ (crc32_pix_in_rsci_din[5])
      ^ (crc32_pix_in_rsci_din[9]) ^ (pix_chan2_rsci_idat_mxwt[9]);
  assign mux_10_nl = MUX_s_1_2_2(xor_389_nl, (~ (crc32_pix_in_rsci_din[10])), fsm_output[5]);
  assign or_294_nl = mux_10_nl | or_tmp_15;
  assign xor_386_nl = xor_cse_341 ^ xor_cse_293 ^ xor_cse_295 ^ xor_cse_317 ^ xor_cse_343
      ^ xor_cse_345 ^ (crc32_pix_in_rsci_din[31]) ^ (pix_chan2_rsci_idat_mxwt[19]);
  assign mux_9_nl = MUX_s_1_2_2(xor_386_nl, (~ (crc32_pix_in_rsci_din[9])), fsm_output[5]);
  assign or_293_nl = mux_9_nl | or_tmp_15;
  assign xor_379_nl = xor_cse_305 ^ xor_cse_337 ^ xor_cse_338 ^ (crc32_pix_in_rsci_din[16])
      ^ (pix_chan2_rsci_idat_mxwt[16]) ^ (crc32_pix_in_rsci_din[11]) ^ (pix_chan2_rsci_idat_mxwt[11])
      ^ (crc32_pix_in_rsci_din[12]) ^ (pix_chan2_rsci_idat_mxwt[12]) ^ (pix_chan2_rsci_idat_mxwt[31]);
  assign mux_8_nl = MUX_s_1_2_2(xor_379_nl, (~ (crc32_pix_in_rsci_din[8])), fsm_output[5]);
  assign or_292_nl = mux_8_nl | or_tmp_15;
  assign xor_373_nl = xor_cse_331 ^ (crc32_pix_in_rsci_din[21]) ^ (pix_chan2_rsci_idat_mxwt[21])
      ^ (crc32_pix_in_rsci_din[24]) ^ xor_cse_326 ^ xor_cse_334 ^ xor_cse_313 ^ (pix_chan2_rsci_idat_mxwt[3])
      ^ (pix_chan2_rsci_idat_mxwt[1]) ^ (crc32_pix_in_rsci_din[4]) ^ (pix_chan2_rsci_idat_mxwt[4]);
  assign mux_7_nl = MUX_s_1_2_2(xor_373_nl, (~ (crc32_pix_in_rsci_din[7])), fsm_output[5]);
  assign or_291_nl = mux_7_nl | or_tmp_15;
  assign xor_367_nl = xor_cse_120 ^ xor_cse_326 ^ xor_cse_327 ^ xor_cse_328 ^ xor_cse_329
      ^ xor_cse_123 ^ (crc32_pix_in_rsci_din[2]) ^ (crc32_pix_in_rsci_din[29]) ^
      (pix_chan2_rsci_idat_mxwt[3]);
  assign mux_6_nl = MUX_s_1_2_2(xor_367_nl, (~ (crc32_pix_in_rsci_din[6])), fsm_output[5]);
  assign or_290_nl = mux_6_nl | or_tmp_15;
  assign xor_361_nl = xor_cse_320 ^ xor_cse_108 ^ xor_cse_300 ^ xor_cse_323 ^ xor_cse_324
      ^ (crc32_pix_in_rsci_din[8]) ^ (crc32_pix_in_rsci_din[12]) ^ (pix_chan2_rsci_idat_mxwt[5]);
  assign mux_5_nl = MUX_s_1_2_2(xor_361_nl, (~ (crc32_pix_in_rsci_din[5])), fsm_output[5]);
  assign or_289_nl = mux_5_nl | or_tmp_15;
  assign xor_354_nl = xor_cse_94 ^ xor_cse_316 ^ xor_cse_295 ^ xor_cse_317 ^ xor_cse_301
      ^ xor_cse_318 ^ (crc32_pix_in_rsci_din[10]) ^ (crc32_pix_in_rsci_din[20]) ^
      (pix_chan2_rsci_idat_mxwt[4]) ^ (pix_chan2_rsci_idat_mxwt[30]);
  assign mux_4_nl = MUX_s_1_2_2(xor_354_nl, (~ (crc32_pix_in_rsci_din[4])), fsm_output[5]);
  assign or_288_nl = mux_4_nl | or_tmp_15;
  assign xor_349_nl = xor_cse_75 ^ xor_cse_294 ^ xor_cse_312 ^ xor_cse_300 ^ xor_cse_313
      ^ (crc32_pix_in_rsci_din[6]) ^ (crc32_pix_in_rsci_din[7]) ^ (pix_chan2_rsci_idat_mxwt[7])
      ^ (crc32_pix_in_rsci_din[25]) ^ (pix_chan2_rsci_idat_mxwt[25]) ^ (crc32_pix_in_rsci_din[19])
      ^ (crc32_pix_in_rsci_din[4]) ^ (pix_chan2_rsci_idat_mxwt[4]);
  assign mux_3_nl = MUX_s_1_2_2(xor_349_nl, (~ (crc32_pix_in_rsci_din[3])), fsm_output[5]);
  assign or_287_nl = mux_3_nl | or_tmp_15;
  assign xor_344_nl = xor_cse_305 ^ xor_cse_308 ^ xor_cse_309 ^ (crc32_pix_in_rsci_din[10])
      ^ (pix_chan2_rsci_idat_mxwt[10]) ^ (crc32_pix_in_rsci_din[5]) ^ (pix_chan2_rsci_idat_mxwt[6])
      ^ (crc32_pix_in_rsci_din[8]) ^ (pix_chan2_rsci_idat_mxwt[8]) ^ (pix_chan2_rsci_idat_mxwt[24]);
  assign mux_2_nl = MUX_s_1_2_2(xor_344_nl, (~ (crc32_pix_in_rsci_din[2])), fsm_output[5]);
  assign or_286_nl = mux_2_nl | or_tmp_15;
  assign xor_336_nl = xor_cse_38 ^ xor_cse_294 ^ xor_cse_300 ^ xor_cse_301 ^ xor_cse_302
      ^ (pix_chan2_rsci_idat_mxwt[4]) ^ (pix_chan2_rsci_idat_mxwt[5]) ^ (crc32_pix_in_rsci_din[8])
      ^ (crc32_pix_in_rsci_din[27]) ^ (crc32_pix_in_rsci_din[21]) ^ (pix_chan2_rsci_idat_mxwt[27]);
  assign mux_1_nl = MUX_s_1_2_2(xor_336_nl, (~ (crc32_pix_in_rsci_din[1])), fsm_output[5]);
  assign or_285_nl = mux_1_nl | or_tmp_15;
  assign xor_330_nl = xor_cse_293 ^ xor_cse_294 ^ xor_cse_295 ^ xor_cse_296 ^ xor_cse_297
      ^ (crc32_pix_in_rsci_din[3]) ^ (pix_chan2_rsci_idat_mxwt[3]) ^ (pix_chan2_rsci_idat_mxwt[6])
      ^ (crc32_pix_in_rsci_din[7]) ^ (crc32_pix_in_rsci_din[2]) ^ (pix_chan2_rsci_idat_mxwt[0])
      ^ (crc32_pix_in_rsci_din[20]);
  assign mux_nl = MUX_s_1_2_2(xor_330_nl, (~ (crc32_pix_in_rsci_din[0])), fsm_output[5]);
  assign or_284_nl = mux_nl | or_tmp_15;
  assign nl_EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_rsci_inst_crc32_pix_in_rsci_dout_run
      = {EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_for_tmp_bit_EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_for_tmp_bit_or_nl
      , or_314_nl , or_313_nl , or_312_nl , or_311_nl , or_310_nl , or_309_nl , or_308_nl
      , or_307_nl , or_306_nl , or_305_nl , or_304_nl , or_303_nl , or_302_nl , or_301_nl
      , or_300_nl , or_299_nl , or_298_nl , or_297_nl , or_296_nl , or_295_nl , or_294_nl
      , or_293_nl , or_292_nl , or_291_nl , or_290_nl , or_289_nl , or_288_nl , or_287_nl
      , or_286_nl , or_285_nl , or_284_nl};
  wire  nl_EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_rsci_inst_run_wten;
  assign nl_EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_rsci_inst_run_wten
      = ~ run_wen;
  wire or_283_nl;
  wire mux1h_63_nl;
  wire EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_1_for_tmp_bit_xor_nl;
  wire EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_2_for_tmp_bit_xor_nl;
  wire or_282_nl;
  wire mux1h_61_nl;
  wire xor_318_nl;
  wire xor_322_nl;
  wire or_281_nl;
  wire mux1h_59_nl;
  wire xor_312_nl;
  wire xor_315_nl;
  wire or_280_nl;
  wire mux1h_57_nl;
  wire xor_305_nl;
  wire xor_308_nl;
  wire or_279_nl;
  wire mux1h_55_nl;
  wire xor_299_nl;
  wire xor_302_nl;
  wire or_278_nl;
  wire mux1h_53_nl;
  wire xor_292_nl;
  wire xor_296_nl;
  wire or_277_nl;
  wire mux1h_51_nl;
  wire xor_285_nl;
  wire xor_288_nl;
  wire or_276_nl;
  wire mux1h_49_nl;
  wire xor_275_nl;
  wire xor_281_nl;
  wire or_275_nl;
  wire mux1h_47_nl;
  wire xor_265_nl;
  wire xor_271_nl;
  wire or_274_nl;
  wire mux1h_45_nl;
  wire xor_259_nl;
  wire xor_261_nl;
  wire or_273_nl;
  wire mux1h_43_nl;
  wire xor_252_nl;
  wire xor_256_nl;
  wire or_272_nl;
  wire mux1h_41_nl;
  wire xor_244_nl;
  wire xor_247_nl;
  wire or_271_nl;
  wire mux1h_39_nl;
  wire xor_236_nl;
  wire xor_241_nl;
  wire or_270_nl;
  wire mux1h_37_nl;
  wire xor_225_nl;
  wire xor_232_nl;
  wire or_269_nl;
  wire mux1h_35_nl;
  wire xor_215_nl;
  wire xor_219_nl;
  wire or_268_nl;
  wire mux1h_33_nl;
  wire xor_205_nl;
  wire xor_210_nl;
  wire or_267_nl;
  wire mux1h_31_nl;
  wire xor_198_nl;
  wire xor_200_nl;
  wire or_266_nl;
  wire mux1h_29_nl;
  wire xor_191_nl;
  wire xor_195_nl;
  wire or_265_nl;
  wire mux1h_27_nl;
  wire xor_178_nl;
  wire xor_184_nl;
  wire or_264_nl;
  wire mux1h_25_nl;
  wire xor_166_nl;
  wire xor_171_nl;
  wire or_263_nl;
  wire mux1h_23_nl;
  wire xor_158_nl;
  wire xor_163_nl;
  wire or_262_nl;
  wire mux1h_21_nl;
  wire xor_149_nl;
  wire xor_152_nl;
  wire or_261_nl;
  wire mux1h_19_nl;
  wire xor_140_nl;
  wire xor_146_nl;
  wire or_260_nl;
  wire mux1h_17_nl;
  wire xor_124_nl;
  wire xor_131_nl;
  wire or_259_nl;
  wire mux1h_15_nl;
  wire xor_113_nl;
  wire xor_118_nl;
  wire or_258_nl;
  wire mux1h_13_nl;
  wire xor_101_nl;
  wire xor_107_nl;
  wire or_257_nl;
  wire mux1h_11_nl;
  wire xor_88_nl;
  wire xor_94_nl;
  wire or_256_nl;
  wire mux1h_9_nl;
  wire xor_73_nl;
  wire xor_81_nl;
  wire or_255_nl;
  wire mux1h_7_nl;
  wire xor_54_nl;
  wire xor_64_nl;
  wire or_254_nl;
  wire mux1h_5_nl;
  wire xor_38_nl;
  wire xor_45_nl;
  wire or_253_nl;
  wire mux1h_3_nl;
  wire xor_20_nl;
  wire xor_28_nl;
  wire or_252_nl;
  wire mux1h_1_nl;
  wire xor_7_nl;
  wire xor_14_nl;
  wire [31:0] nl_EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_rsci_inst_crc32_dat_out_rsci_dout_run;
  assign EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_1_for_tmp_bit_xor_nl = xor_cse_148
      ^ xor_cse_47 ^ xor_cse_1 ^ xor_cse_150 ^ xor_cse_264 ^ (crc32_dat_out_rsci_din[21])
      ^ (MCOL_qr_10_lpi_3_dfm_1[5]) ^ (crc32_dat_out_rsci_din[22]) ^ (crc32_dat_out_rsci_din[25])
      ^ (MCOL_qr_8_lpi_3_dfm_1[1]) ^ (crc32_dat_out_rsci_din[0]);
  assign EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_2_for_tmp_bit_xor_nl = xor_cse_74
      ^ (crc32_dat_out_rsci_din[2]) ^ (pix_chan2_rsci_idat_mxwt[2]) ^ (crc32_dat_out_rsci_din[0])
      ^ (pix_chan2_rsci_idat_mxwt[25]) ^ xor_cse_156 ^ xor_cse_148 ^ xor_cse_170
      ^ xor_cse_133;
  assign mux1h_63_nl = MUX1HOT_s_1_3_2(EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_1_for_tmp_bit_xor_nl,
      EdgeDetect_IP_EdgeDetect_MagAng_calc_crc32_32_2_for_tmp_bit_xor_nl, (~ (crc32_dat_out_rsci_din[31])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_283_nl = mux1h_63_nl | or_tmp_15;
  assign xor_318_nl = xor_cse_148 ^ xor_cse_48 ^ xor_cse_126 ^ xor_cse_150 ^ xor_cse_211
      ^ (crc32_dat_out_rsci_din[20]) ^ (MCOL_qr_8_lpi_3_dfm_1[4]) ^ (crc32_dat_out_rsci_din[14])
      ^ (MCOL_qr_11_lpi_3_dfm_1[6]) ^ (MCOL_qr_8_lpi_3_dfm_1[3]) ^ (crc32_dat_out_rsci_din[22])
      ^ (MCOL_qr_10_lpi_3_dfm_1[6]);
  assign xor_322_nl = xor_cse_154 ^ (crc32_dat_out_rsci_din[14]) ^ (pix_chan2_rsci_idat_mxwt[24])
      ^ (crc32_dat_out_rsci_din[22]) ^ xor_cse_144 ^ xor_cse_126 ^ xor_cse_23 ^ xor_cse_292;
  assign mux1h_61_nl = MUX1HOT_s_1_3_2(xor_318_nl, xor_322_nl, (~ (crc32_dat_out_rsci_din[30])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_282_nl = mux1h_61_nl | or_tmp_15;
  assign xor_312_nl = xor_cse_216 ^ (crc32_dat_out_rsci_din[0]) ^ xor_cse_47 ^ xor_cse_125
      ^ xor_cse_136 ^ xor_cse_164 ^ xor_cse_32 ^ (crc32_dat_out_rsci_din[18]) ^ (MCOL_qr_10_lpi_3_dfm_1[2])
      ^ (MCOL_qr_11_lpi_3_dfm_1[0]) ^ (crc32_dat_out_rsci_din[7]);
  assign xor_315_nl = xor_cse_156 ^ xor_cse_131 ^ xor_cse_179 ^ xor_cse_121 ^ xor_cse_164
      ^ xor_cse_225 ^ (pix_chan2_rsci_idat_mxwt[23]) ^ (crc32_dat_out_rsci_din[30])
      ^ (crc32_dat_out_rsci_din[31]) ^ (crc32_dat_out_rsci_din[7]) ^ (crc32_dat_out_rsci_din[5])
      ^ (pix_chan2_rsci_idat_mxwt[5]) ^ (pix_chan2_rsci_idat_mxwt[1]) ^ (crc32_dat_out_rsci_din[0]);
  assign mux1h_59_nl = MUX1HOT_s_1_3_2(xor_312_nl, xor_315_nl, (~ (crc32_dat_out_rsci_din[29])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_281_nl = mux1h_59_nl | or_tmp_15;
  assign xor_305_nl = xor_cse_135 ^ xor_cse_125 ^ xor_cse_100 ^ xor_cse_127 ^ xor_cse_256
      ^ xor_cse_51 ^ (crc32_dat_out_rsci_din[28]) ^ (MCOL_qr_10_lpi_3_dfm_1[0]) ^
      (MCOL_qr_10_lpi_3_dfm_1[6]) ^ (MCOL_qr_10_lpi_3_dfm_1[1]) ^ (crc32_dat_out_rsci_din[21])
      ^ (MCOL_qr_10_lpi_3_dfm_1[5]);
  assign xor_308_nl = xor_cse_221 ^ (pix_chan2_rsci_idat_mxwt[22]) ^ (crc32_dat_out_rsci_din[29])
      ^ (crc32_dat_out_rsci_din[6]) ^ (pix_chan2_rsci_idat_mxwt[21]) ^ xor_cse_135
      ^ xor_cse_205 ^ xor_cse_169 ^ xor_cse_40;
  assign mux1h_57_nl = MUX1HOT_s_1_3_2(xor_305_nl, xor_308_nl, (~ (crc32_dat_out_rsci_din[28])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_280_nl = mux1h_57_nl | or_tmp_15;
  assign xor_299_nl = xor_cse_84 ^ xor_cse_114 ^ xor_cse_100 ^ xor_cse_88 ^ xor_cse_102
      ^ xor_cse_71 ^ xor_cse_234 ^ (MCOL_qr_9_lpi_3_dfm_1[5]) ^ (MCOL_qr_10_lpi_3_dfm_1[7])
      ^ (MCOL_qr_11_lpi_3_dfm_1[5]) ^ (MCOL_qr_8_lpi_3_dfm_1[2]) ^ (crc32_dat_out_rsci_din[1])
      ^ (MCOL_qr_8_lpi_3_dfm_1[1]) ^ (crc32_dat_out_rsci_din[0]) ^ (MCOL_qr_11_lpi_3_dfm_1[1]);
  assign xor_302_nl = xor_cse_120 ^ xor_cse_109 ^ xor_cse_114 ^ xor_cse_168 ^ xor_cse_253
      ^ xor_cse_102 ^ xor_cse_81 ^ (crc32_dat_out_rsci_din[11]) ^ (pix_chan2_rsci_idat_mxwt[11])
      ^ (crc32_dat_out_rsci_din[28]) ^ (crc32_dat_out_rsci_din[12]) ^ (crc32_dat_out_rsci_din[6])
      ^ (crc32_dat_out_rsci_din[0]) ^ (pix_chan2_rsci_idat_mxwt[25]);
  assign mux1h_55_nl = MUX1HOT_s_1_3_2(xor_299_nl, xor_302_nl, (~ (crc32_dat_out_rsci_din[27])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_279_nl = mux1h_55_nl | or_tmp_15;
  assign xor_292_nl = xor_cse_83 ^ (MCOL_qr_8_lpi_3_dfm_1[3]) ^ (crc32_dat_out_rsci_din[21])
      ^ (MCOL_qr_10_lpi_3_dfm_1[5]) ^ (MCOL_qr_11_lpi_3_dfm_1[7]) ^ xor_cse_48 ^
      xor_cse_172 ^ xor_cse_89 ^ (MCOL_qr_9_lpi_3_dfm_1[3]) ^ (crc32_dat_out_rsci_din[31])
      ^ (MCOL_qr_8_lpi_3_dfm_1[2]) ^ (crc32_dat_out_rsci_din[3]);
  assign xor_296_nl = xor_cse_93 ^ xor_cse_223 ^ (crc32_dat_out_rsci_din[3]) ^ xor_cse_142
      ^ xor_cse_144 ^ xor_cse_254 ^ (crc32_dat_out_rsci_din[28]) ^ (crc32_dat_out_rsci_din[24])
      ^ (pix_chan2_rsci_idat_mxwt[18]) ^ (pix_chan2_rsci_idat_mxwt[24]);
  assign mux1h_53_nl = MUX1HOT_s_1_3_2(xor_292_nl, xor_296_nl, (~ (crc32_dat_out_rsci_din[26])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_278_nl = mux1h_53_nl | or_tmp_15;
  assign xor_285_nl = xor_cse_179 ^ xor_cse_88 ^ xor_cse_68 ^ xor_cse_192 ^ xor_cse_264
      ^ xor_cse_248 ^ (crc32_dat_out_rsci_din[26]) ^ (crc32_dat_out_rsci_din[10])
      ^ (crc32_dat_out_rsci_din[27]) ^ (MCOL_qr_11_lpi_3_dfm_1[3]) ^ (MCOL_qr_11_lpi_3_dfm_1[5])
      ^ (MCOL_qr_11_lpi_3_dfm_1[0]);
  assign xor_288_nl = xor_cse_131 ^ xor_cse_179 ^ xor_cse_77 ^ xor_cse_98 ^ xor_cse_78
      ^ xor_cse_79 ^ xor_cse_267 ^ (crc32_dat_out_rsci_din[23]) ^ (crc32_dat_out_rsci_din[1])
      ^ (crc32_dat_out_rsci_din[2]);
  assign mux1h_51_nl = MUX1HOT_s_1_3_2(xor_285_nl, xor_288_nl, (~ (crc32_dat_out_rsci_din[25])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_277_nl = mux1h_51_nl | or_tmp_15;
  assign xor_275_nl = xor_cse_85 ^ xor_cse_1 ^ xor_cse_172 ^ xor_cse_101 ^ xor_cse_137
      ^ xor_cse_256 ^ (MCOL_qr_9_lpi_3_dfm_1[0]) ^ (crc32_dat_out_rsci_din[9]) ^
      (MCOL_qr_9_lpi_3_dfm_1[2]) ^ (MCOL_qr_11_lpi_3_dfm_1[2]) ^ (MCOL_qr_11_lpi_3_dfm_1[5])
      ^ (crc32_dat_out_rsci_din[31]) ^ (MCOL_qr_8_lpi_3_dfm_1[7]) ^ (MCOL_qr_11_lpi_3_dfm_1[7]);
  assign xor_281_nl = xor_cse_259 ^ xor_cse_85 ^ xor_cse_120 ^ xor_cse_77 ^ xor_cse_240
      ^ xor_cse_206 ^ (crc32_dat_out_rsci_din[8]) ^ (pix_chan2_rsci_idat_mxwt[10])
      ^ (crc32_dat_out_rsci_din[16]) ^ (crc32_dat_out_rsci_din[23]) ^ (pix_chan2_rsci_idat_mxwt[29])
      ^ (crc32_dat_out_rsci_din[21]);
  assign mux1h_49_nl = MUX1HOT_s_1_3_2(xor_275_nl, xor_281_nl, (~ (crc32_dat_out_rsci_din[24])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_276_nl = mux1h_49_nl | or_tmp_15;
  assign xor_265_nl = xor_cse_45 ^ xor_cse_136 ^ xor_cse_163 ^ xor_cse_101 ^ xor_cse_248
      ^ (MCOL_qr_10_lpi_3_dfm_1[7]) ^ (MCOL_qr_9_lpi_3_dfm_1[0]) ^ (MCOL_qr_11_lpi_3_dfm_1[4])
      ^ (MCOL_qr_10_lpi_3_dfm_1[4]) ^ (MCOL_qr_8_lpi_3_dfm_1[3]) ^ (MCOL_qr_8_lpi_3_dfm_1[0]);
  assign xor_271_nl = xor_cse_222 ^ (pix_chan2_rsci_idat_mxwt[0]) ^ (crc32_dat_out_rsci_din[19])
      ^ xor_cse_253 ^ xor_cse_169 ^ xor_cse_254 ^ (crc32_dat_out_rsci_din[8]) ^ (pix_chan2_rsci_idat_mxwt[8])
      ^ (crc32_dat_out_rsci_din[20]) ^ (pix_chan2_rsci_idat_mxwt[30]);
  assign mux1h_47_nl = MUX1HOT_s_1_3_2(xor_265_nl, xor_271_nl, (~ (crc32_dat_out_rsci_din[23])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_275_nl = mux1h_47_nl | or_tmp_15;
  assign xor_259_nl = (MCOL_qr_10_lpi_3_dfm_1[4]) ^ xor_cse_125 ^ xor_cse_163 ^ xor_cse_9
      ^ xor_cse_159 ^ xor_cse_245 ^ (crc32_dat_out_rsci_din[22]) ^ (MCOL_qr_9_lpi_3_dfm_1[0])
      ^ (crc32_dat_out_rsci_din[26]) ^ (crc32_dat_out_rsci_din[30]);
  assign xor_261_nl = (pix_chan2_rsci_idat_mxwt[30]) ^ xor_cse_98 ^ xor_cse_195 ^
      xor_cse_201 ^ xor_cse_161 ^ xor_cse_245 ^ (pix_chan2_rsci_idat_mxwt[20]) ^
      (pix_chan2_rsci_idat_mxwt[27]) ^ (pix_chan2_rsci_idat_mxwt[19]) ^ (pix_chan2_rsci_idat_mxwt[29]);
  assign mux1h_45_nl = MUX1HOT_s_1_3_2(xor_259_nl, xor_261_nl, (~ (crc32_dat_out_rsci_din[22])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_274_nl = mux1h_45_nl | or_tmp_15;
  assign xor_252_nl = xor_cse_146 ^ (MCOL_qr_8_lpi_3_dfm_1[3]) ^ (MCOL_qr_9_lpi_3_dfm_1[7])
      ^ (MCOL_qr_11_lpi_3_dfm_1[7]) ^ xor_cse_8 ^ xor_cse_240 ^ xor_cse_219 ^ (MCOL_qr_11_lpi_3_dfm_1[4])
      ^ (crc32_dat_out_rsci_din[17]) ^ (MCOL_qr_11_lpi_3_dfm_1[5]) ^ (MCOL_qr_8_lpi_3_dfm_1[2]);
  assign xor_256_nl = xor_cse_57 ^ xor_cse_142 ^ xor_cse_8 ^ xor_cse_240 ^ (pix_chan2_rsci_idat_mxwt[26])
      ^ (crc32_dat_out_rsci_din[18]) ^ (pix_chan2_rsci_idat_mxwt[28]) ^ (crc32_dat_out_rsci_din[17])
      ^ (pix_chan2_rsci_idat_mxwt[17]) ^ (pix_chan2_rsci_idat_mxwt[29]) ^ (pix_chan2_rsci_idat_mxwt[3])
      ^ (crc32_dat_out_rsci_din[5]) ^ (crc32_dat_out_rsci_din[15]) ^ (pix_chan2_rsci_idat_mxwt[15]);
  assign mux1h_43_nl = MUX1HOT_s_1_3_2(xor_252_nl, xor_256_nl, (~ (crc32_dat_out_rsci_din[21])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_273_nl = mux1h_43_nl | or_tmp_15;
  assign xor_244_nl = xor_cse_135 ^ xor_cse_148 ^ xor_cse_47 ^ xor_cse_84 ^ xor_cse_1
      ^ xor_cse_127 ^ xor_cse_202 ^ xor_cse_234 ^ (MCOL_qr_10_lpi_3_dfm_1[1]) ^ (MCOL_qr_11_lpi_3_dfm_1[4])
      ^ (MCOL_qr_11_lpi_3_dfm_1[6]);
  assign xor_247_nl = xor_cse_156 ^ xor_cse_135 ^ xor_cse_75 ^ xor_cse_148 ^ xor_cse_132
      ^ xor_cse_39 ^ xor_cse_205 ^ (crc32_dat_out_rsci_din[17]) ^ (pix_chan2_rsci_idat_mxwt[17])
      ^ (crc32_dat_out_rsci_din[14]) ^ (pix_chan2_rsci_idat_mxwt[14]) ^ (pix_chan2_rsci_idat_mxwt[30])
      ^ (crc32_dat_out_rsci_din[6]);
  assign mux1h_41_nl = MUX1HOT_s_1_3_2(xor_244_nl, xor_247_nl, (~ (crc32_dat_out_rsci_din[20])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_272_nl = mux1h_41_nl | or_tmp_15;
  assign xor_236_nl = xor_cse_189 ^ xor_cse_125 ^ xor_cse_136 ^ xor_cse_163 ^ xor_cse_182
      ^ xor_cse_193 ^ (MCOL_qr_10_lpi_3_dfm_1[0]) ^ (crc32_dat_out_rsci_din[29])
      ^ (MCOL_qr_8_lpi_3_dfm_1[7]) ^ (MCOL_qr_8_lpi_3_dfm_1[0]);
  assign xor_241_nl = xor_cse_140 ^ xor_cse_156 ^ xor_cse_168 ^ xor_cse_144 ^ xor_cse_121
      ^ xor_cse_185 ^ (crc32_dat_out_rsci_din[26]) ^ (pix_chan2_rsci_idat_mxwt[26])
      ^ (pix_chan2_rsci_idat_mxwt[27]) ^ (crc32_dat_out_rsci_din[29]) ^ (pix_chan2_rsci_idat_mxwt[4])
      ^ (pix_chan2_rsci_idat_mxwt[18]) ^ (pix_chan2_rsci_idat_mxwt[19]);
  assign mux1h_39_nl = MUX1HOT_s_1_3_2(xor_236_nl, xor_241_nl, (~ (crc32_dat_out_rsci_din[19])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_271_nl = mux1h_39_nl | or_tmp_15;
  assign xor_225_nl = xor_cse_216 ^ (MCOL_qr_8_lpi_3_dfm_1[6]) ^ xor_cse_45 ^ xor_cse_125
      ^ xor_cse_100 ^ xor_cse_26 ^ xor_cse_219 ^ (MCOL_qr_9_lpi_3_dfm_1[1]) ^ (crc32_dat_out_rsci_din[26])
      ^ (MCOL_qr_10_lpi_3_dfm_1[1]) ^ (crc32_dat_out_rsci_din[6]);
  assign xor_232_nl = xor_cse_221 ^ xor_cse_222 ^ (crc32_dat_out_rsci_din[6]) ^ xor_cse_179
      ^ xor_cse_225 ^ (crc32_dat_out_rsci_din[15]) ^ (crc32_dat_out_rsci_din[26])
      ^ (pix_chan2_rsci_idat_mxwt[26]) ^ (crc32_dat_out_rsci_din[30]);
  assign mux1h_37_nl = MUX1HOT_s_1_3_2(xor_225_nl, xor_232_nl, (~ (crc32_dat_out_rsci_din[18])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_270_nl = mux1h_37_nl | or_tmp_15;
  assign xor_215_nl = xor_cse_63 ^ (MCOL_qr_11_lpi_3_dfm_1[4]) ^ xor_cse_179 ^ xor_cse_114
      ^ xor_cse_115 ^ xor_cse_183 ^ xor_cse_211 ^ (MCOL_qr_9_lpi_3_dfm_1[0]) ^ (crc32_dat_out_rsci_din[27])
      ^ (MCOL_qr_11_lpi_3_dfm_1[3]) ^ (crc32_dat_out_rsci_din[28]);
  assign xor_219_nl = xor_cse_174 ^ (crc32_dat_out_rsci_din[14]) ^ (pix_chan2_rsci_idat_mxwt[8])
      ^ (pix_chan2_rsci_idat_mxwt[27]) ^ (pix_chan2_rsci_idat_mxwt[12]) ^ xor_cse_179
      ^ xor_cse_97 ^ xor_cse_215 ^ xor_cse_112;
  assign mux1h_35_nl = MUX1HOT_s_1_3_2(xor_215_nl, xor_219_nl, (~ (crc32_dat_out_rsci_din[17])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_269_nl = mux1h_35_nl | or_tmp_15;
  assign xor_205_nl = xor_cse ^ xor_cse_84 ^ xor_cse_172 ^ xor_cse_68 ^ xor_cse_201
      ^ xor_cse_202 ^ (MCOL_qr_9_lpi_3_dfm_1[5]) ^ (crc32_dat_out_rsci_din[10]) ^
      (crc32_dat_out_rsci_din[15]) ^ (MCOL_qr_8_lpi_3_dfm_1[4]) ^ (MCOL_qr_10_lpi_3_dfm_1[0])
      ^ (MCOL_qr_10_lpi_3_dfm_1[6]);
  assign xor_210_nl = xor_cse ^ xor_cse_94 ^ xor_cse_132 ^ xor_cse_201 ^ xor_cse_205
      ^ xor_cse_206 ^ (pix_chan2_rsci_idat_mxwt[13]) ^ (pix_chan2_rsci_idat_mxwt[23])
      ^ (crc32_dat_out_rsci_din[10]) ^ (crc32_dat_out_rsci_din[27]) ^ (pix_chan2_rsci_idat_mxwt[1])
      ^ (pix_chan2_rsci_idat_mxwt[19]) ^ (pix_chan2_rsci_idat_mxwt[22]);
  assign mux1h_33_nl = MUX1HOT_s_1_3_2(xor_205_nl, xor_210_nl, (~ (crc32_dat_out_rsci_din[16])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_268_nl = mux1h_33_nl | or_tmp_15;
  assign xor_198_nl = xor_cse_85 ^ xor_cse_136 ^ xor_cse_68 ^ xor_cse_163 ^ xor_cse_29
      ^ (crc32_dat_out_rsci_din[12]) ^ (MCOL_qr_9_lpi_3_dfm_1[4]) ^ (crc32_dat_out_rsci_din[23])
      ^ (crc32_dat_out_rsci_din[18]) ^ (MCOL_qr_10_lpi_3_dfm_1[2]) ^ (MCOL_qr_8_lpi_3_dfm_1[7])
      ^ (MCOL_qr_8_lpi_3_dfm_1[2]) ^ (crc32_dat_out_rsci_din[1]);
  assign xor_200_nl = (pix_chan2_rsci_idat_mxwt[19]) ^ xor_cse_85 ^ xor_cse_94 ^
      xor_cse_142 ^ xor_cse_168 ^ xor_cse_169 ^ xor_cse_42 ^ (crc32_dat_out_rsci_din[18])
      ^ (pix_chan2_rsci_idat_mxwt[18]) ^ (crc32_dat_out_rsci_din[31]) ^ (crc32_dat_out_rsci_din[5]);
  assign mux1h_31_nl = MUX1HOT_s_1_3_2(xor_198_nl, xor_200_nl, (~ (crc32_dat_out_rsci_din[15])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_267_nl = mux1h_31_nl | or_tmp_15;
  assign xor_191_nl = xor_cse_189 ^ (MCOL_qr_8_lpi_3_dfm_1[0]) ^ (MCOL_qr_11_lpi_3_dfm_1[6])
      ^ xor_cse_192 ^ xor_cse_193 ^ xor_cse_103 ^ (crc32_dat_out_rsci_din[8]) ^ (crc32_dat_out_rsci_din[13])
      ^ (crc32_dat_out_rsci_din[17]) ^ (MCOL_qr_8_lpi_3_dfm_1[6]);
  assign xor_195_nl = xor_cse_135 ^ xor_cse_144 ^ xor_cse_77 ^ xor_cse_195 ^ xor_cse_24
      ^ (crc32_dat_out_rsci_din[11]) ^ (pix_chan2_rsci_idat_mxwt[11]) ^ (crc32_dat_out_rsci_din[13])
      ^ (crc32_dat_out_rsci_din[26]) ^ (crc32_dat_out_rsci_din[17]) ^ (pix_chan2_rsci_idat_mxwt[17])
      ^ (crc32_dat_out_rsci_din[1]) ^ (pix_chan2_rsci_idat_mxwt[0]);
  assign mux1h_29_nl = MUX1HOT_s_1_3_2(xor_191_nl, xor_195_nl, (~ (crc32_dat_out_rsci_din[14])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_266_nl = mux1h_29_nl | or_tmp_15;
  assign xor_178_nl = xor_cse_178 ^ (MCOL_qr_8_lpi_3_dfm_1[7]) ^ (MCOL_qr_9_lpi_3_dfm_1[0])
      ^ (MCOL_qr_10_lpi_3_dfm_1[0]) ^ (MCOL_qr_8_lpi_3_dfm_1[0]) ^ xor_cse_65 ^ xor_cse_26
      ^ xor_cse_182 ^ xor_cse_183;
  assign xor_184_nl = xor_cse_178 ^ (pix_chan2_rsci_idat_mxwt[16]) ^ xor_cse_38 ^
      xor_cse_97 ^ xor_cse_185 ^ xor_cse_187 ^ (crc32_dat_out_rsci_din[21]) ^ (pix_chan2_rsci_idat_mxwt[12])
      ^ (pix_chan2_rsci_idat_mxwt[24]) ^ (crc32_dat_out_rsci_din[16]);
  assign mux1h_27_nl = MUX1HOT_s_1_3_2(xor_178_nl, xor_184_nl, (~ (crc32_dat_out_rsci_din[13])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_265_nl = mux1h_27_nl | or_tmp_15;
  assign xor_166_nl = xor_cse_114 ^ xor_cse_172 ^ xor_cse_88 ^ xor_cse_137 ^ xor_cse_69
      ^ (crc32_dat_out_rsci_din[7]) ^ (crc32_dat_out_rsci_din[11]) ^ (MCOL_qr_10_lpi_3_dfm_1[7])
      ^ (crc32_dat_out_rsci_din[4]);
  assign xor_171_nl = xor_cse_174 ^ xor_cse_132 ^ xor_cse_58 ^ (crc32_dat_out_rsci_din[9])
      ^ (pix_chan2_rsci_idat_mxwt[9]) ^ (crc32_dat_out_rsci_din[7]) ^ (pix_chan2_rsci_idat_mxwt[7])
      ^ (crc32_dat_out_rsci_din[15]) ^ (crc32_dat_out_rsci_din[4]);
  assign mux1h_25_nl = MUX1HOT_s_1_3_2(xor_166_nl, xor_171_nl, (~ (crc32_dat_out_rsci_din[12])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_264_nl = mux1h_25_nl | or_tmp_15;
  assign xor_158_nl = xor_cse_1 ^ xor_cse_163 ^ xor_cse_164 ^ (crc32_dat_out_rsci_din[8])
      ^ (MCOL_qr_9_lpi_3_dfm_1[0]) ^ (crc32_dat_out_rsci_din[5]) ^ (MCOL_qr_8_lpi_3_dfm_1[5])
      ^ (crc32_dat_out_rsci_din[10]) ^ (MCOL_qr_9_lpi_3_dfm_1[2]) ^ (MCOL_qr_10_lpi_3_dfm_1[6])
      ^ (crc32_dat_out_rsci_din[14]) ^ (MCOL_qr_9_lpi_3_dfm_1[6]) ^ (MCOL_qr_10_lpi_3_dfm_1[7])
      ^ (MCOL_qr_8_lpi_3_dfm_1[1]) ^ (MCOL_qr_9_lpi_3_dfm_1[7]);
  assign xor_163_nl = xor_cse_75 ^ xor_cse_168 ^ xor_cse_169 ^ xor_cse_170 ^ xor_cse_60
      ^ (pix_chan2_rsci_idat_mxwt[22]) ^ (crc32_dat_out_rsci_din[3]) ^ (crc32_dat_out_rsci_din[15])
      ^ (pix_chan2_rsci_idat_mxwt[27]);
  assign mux1h_23_nl = MUX1HOT_s_1_3_2(xor_158_nl, xor_163_nl, (~ (crc32_dat_out_rsci_din[11])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_263_nl = mux1h_23_nl | or_tmp_15;
  assign xor_149_nl = (MCOL_qr_11_lpi_3_dfm_1[2]) ^ xor_cse_47 ^ xor_cse_8 ^ xor_cse_69
      ^ xor_cse_159 ^ xor_cse_152 ^ (crc32_dat_out_rsci_din[21]) ^ (MCOL_qr_10_lpi_3_dfm_1[5])
      ^ (crc32_dat_out_rsci_din[14]) ^ (MCOL_qr_9_lpi_3_dfm_1[6]);
  assign xor_152_nl = xor_cse_57 ^ xor_cse_8 ^ xor_cse_121 ^ xor_cse_59 ^ xor_cse_161
      ^ (crc32_dat_out_rsci_din[4]) ^ (crc32_dat_out_rsci_din[21]) ^ (crc32_dat_out_rsci_din[9])
      ^ (pix_chan2_rsci_idat_mxwt[21]);
  assign mux1h_21_nl = MUX1HOT_s_1_3_2(xor_149_nl, xor_152_nl, (~ (crc32_dat_out_rsci_din[10])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_262_nl = mux1h_21_nl | or_tmp_15;
  assign xor_140_nl = xor_cse_146 ^ xor_cse_148 ^ xor_cse_4 ^ xor_cse_149 ^ xor_cse_150
      ^ xor_cse_152 ^ (crc32_dat_out_rsci_din[20]) ^ (MCOL_qr_10_lpi_3_dfm_1[4]);
  assign xor_146_nl = xor_cse_154 ^ (pix_chan2_rsci_idat_mxwt[19]) ^ xor_cse_156
      ^ xor_cse_97 ^ xor_cse_149 ^ xor_cse_99 ^ (pix_chan2_rsci_idat_mxwt[17]) ^
      (crc32_dat_out_rsci_din[13]) ^ (pix_chan2_rsci_idat_mxwt[13]) ^ (pix_chan2_rsci_idat_mxwt[2]);
  assign mux1h_19_nl = MUX1HOT_s_1_3_2(xor_140_nl, xor_146_nl, (~ (crc32_dat_out_rsci_din[9])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_261_nl = mux1h_19_nl | or_tmp_15;
  assign xor_124_nl = xor_cse_135 ^ xor_cse_47 ^ xor_cse_48 ^ xor_cse_136 ^ xor_cse_137
      ^ (crc32_dat_out_rsci_din[16]) ^ (crc32_dat_out_rsci_din[11]) ^ (MCOL_qr_9_lpi_3_dfm_1[3])
      ^ (crc32_dat_out_rsci_din[12]) ^ (MCOL_qr_9_lpi_3_dfm_1[4]) ^ (MCOL_qr_8_lpi_3_dfm_1[4])
      ^ (MCOL_qr_11_lpi_3_dfm_1[6]) ^ (crc32_dat_out_rsci_din[2]);
  assign xor_131_nl = xor_cse_140 ^ (crc32_dat_out_rsci_din[15]) ^ xor_cse_57 ^ xor_cse_142
      ^ xor_cse_132 ^ xor_cse_144 ^ (crc32_dat_out_rsci_din[14]) ^ (pix_chan2_rsci_idat_mxwt[14])
      ^ (crc32_dat_out_rsci_din[2]) ^ (crc32_dat_out_rsci_din[5]);
  assign mux1h_17_nl = MUX1HOT_s_1_3_2(xor_124_nl, xor_131_nl, (~ (crc32_dat_out_rsci_din[8])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_260_nl = mux1h_17_nl | or_tmp_15;
  assign xor_113_nl = xor_cse_125 ^ xor_cse_26 ^ xor_cse_126 ^ xor_cse_127 ^ xor_cse_117
      ^ (crc32_dat_out_rsci_din[15]) ^ (MCOL_qr_9_lpi_3_dfm_1[7]) ^ (crc32_dat_out_rsci_din[11])
      ^ (MCOL_qr_9_lpi_3_dfm_1[3]) ^ (MCOL_qr_10_lpi_3_dfm_1[1]) ^ (crc32_dat_out_rsci_din[1])
      ^ (MCOL_qr_8_lpi_3_dfm_1[1]);
  assign xor_118_nl = xor_cse_131 ^ xor_cse_132 ^ xor_cse_121 ^ xor_cse_126 ^ xor_cse_122
      ^ xor_cse_133 ^ (crc32_dat_out_rsci_din[15]) ^ (crc32_dat_out_rsci_din[17]);
  assign mux1h_15_nl = MUX1HOT_s_1_3_2(xor_113_nl, xor_118_nl, (~ (crc32_dat_out_rsci_din[7])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_259_nl = mux1h_15_nl | or_tmp_15;
  assign xor_101_nl = xor_cse_44 ^ (MCOL_qr_11_lpi_3_dfm_1[5]) ^ xor_cse_114 ^ xor_cse_100
      ^ xor_cse_115 ^ xor_cse_117 ^ (MCOL_qr_9_lpi_3_dfm_1[6]) ^ (MCOL_qr_10_lpi_3_dfm_1[4])
      ^ (crc32_dat_out_rsci_din[13]) ^ (MCOL_qr_9_lpi_3_dfm_1[5]);
  assign xor_107_nl = xor_cse_120 ^ xor_cse_45 ^ xor_cse_114 ^ xor_cse_121 ^ xor_cse_122
      ^ xor_cse_123 ^ (pix_chan2_rsci_idat_mxwt[9]) ^ (crc32_dat_out_rsci_din[12])
      ^ (pix_chan2_rsci_idat_mxwt[0]);
  assign mux1h_13_nl = MUX1HOT_s_1_3_2(xor_101_nl, xor_107_nl, (~ (crc32_dat_out_rsci_din[6])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_258_nl = mux1h_13_nl | or_tmp_15;
  assign xor_88_nl = xor_cse_45 ^ xor_cse_84 ^ xor_cse_100 ^ xor_cse_101 ^ xor_cse_102
      ^ xor_cse_103 ^ (MCOL_qr_8_lpi_3_dfm_1[3]) ^ (crc32_dat_out_rsci_din[5]) ^
      (MCOL_qr_8_lpi_3_dfm_1[5]) ^ (MCOL_qr_8_lpi_3_dfm_1[6]) ^ (MCOL_qr_11_lpi_3_dfm_1[1])
      ^ (MCOL_qr_11_lpi_3_dfm_1[7]);
  assign xor_94_nl = xor_cse_108 ^ (pix_chan2_rsci_idat_mxwt[9]) ^ (pix_chan2_rsci_idat_mxwt[28])
      ^ (crc32_dat_out_rsci_din[21]) ^ (crc32_dat_out_rsci_din[6]) ^ xor_cse_45 ^
      xor_cse_97 ^ xor_cse_102 ^ xor_cse_112;
  assign mux1h_11_nl = MUX1HOT_s_1_3_2(xor_88_nl, xor_94_nl, (~ (crc32_dat_out_rsci_din[5])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_257_nl = mux1h_11_nl | or_tmp_15;
  assign xor_73_nl = xor_cse_83 ^ (crc32_dat_out_rsci_din[24]) ^ (MCOL_qr_11_lpi_3_dfm_1[0])
      ^ xor_cse_4 ^ xor_cse_88 ^ xor_cse_89 ^ (crc32_dat_out_rsci_din[20]) ^ (crc32_dat_out_rsci_din[4])
      ^ (crc32_dat_out_rsci_din[5]) ^ (MCOL_qr_8_lpi_3_dfm_1[5]);
  assign xor_81_nl = xor_cse_93 ^ (pix_chan2_rsci_idat_mxwt[4]) ^ (pix_chan2_rsci_idat_mxwt[30])
      ^ xor_cse_97 ^ xor_cse_98 ^ xor_cse_58 ^ xor_cse_99;
  assign mux1h_9_nl = MUX1HOT_s_1_3_2(xor_73_nl, xor_81_nl, (~ (crc32_dat_out_rsci_din[4])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_256_nl = mux1h_9_nl | or_tmp_15;
  assign xor_54_nl = xor_cse_63 ^ xor_cse ^ xor_cse_1 ^ xor_cse_68 ^ xor_cse_69 ^
      xor_cse_71 ^ (crc32_dat_out_rsci_din[25]) ^ (crc32_dat_out_rsci_din[26]) ^
      (crc32_dat_out_rsci_din[10]);
  assign xor_64_nl = xor_cse_74 ^ xor_cse ^ xor_cse_77 ^ xor_cse_78 ^ xor_cse_79
      ^ xor_cse_81 ^ (crc32_dat_out_rsci_din[5]) ^ (crc32_dat_out_rsci_din[19]) ^
      (pix_chan2_rsci_idat_mxwt[4]);
  assign mux1h_7_nl = MUX1HOT_s_1_3_2(xor_54_nl, xor_64_nl, (~ (crc32_dat_out_rsci_din[3])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_255_nl = mux1h_7_nl | or_tmp_15;
  assign xor_38_nl = xor_cse_44 ^ xor_cse_47 ^ xor_cse_48 ^ xor_cse_4 ^ xor_cse_51
      ^ (crc32_dat_out_rsci_din[10]) ^ (MCOL_qr_9_lpi_3_dfm_1[2]) ^ (crc32_dat_out_rsci_din[4])
      ^ (crc32_dat_out_rsci_din[2]) ^ (crc32_dat_out_rsci_din[22]) ^ (MCOL_qr_11_lpi_3_dfm_1[4]);
  assign xor_45_nl = xor_cse_45 ^ xor_cse_57 ^ xor_cse_58 ^ xor_cse_59 ^ xor_cse_60
      ^ (crc32_dat_out_rsci_din[25]) ^ (pix_chan2_rsci_idat_mxwt[25]) ^ (crc32_dat_out_rsci_din[4])
      ^ (crc32_dat_out_rsci_din[18]) ^ (crc32_dat_out_rsci_din[2]) ^ (pix_chan2_rsci_idat_mxwt[3])
      ^ (crc32_dat_out_rsci_din[22]) ^ (pix_chan2_rsci_idat_mxwt[28]);
  assign mux1h_5_nl = MUX1HOT_s_1_3_2(xor_38_nl, xor_45_nl, (~ (crc32_dat_out_rsci_din[2])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_254_nl = mux1h_5_nl | or_tmp_15;
  assign xor_20_nl = xor_cse ^ xor_cse_4 ^ xor_cse_26 ^ xor_cse_29 ^ xor_cse_32 ^
      (crc32_dat_out_rsci_din[24]) ^ (crc32_dat_out_rsci_din[27]) ^ (crc32_dat_out_rsci_din[3])
      ^ (crc32_dat_out_rsci_din[17]) ^ (crc32_dat_out_rsci_din[2]) ^ (MCOL_qr_11_lpi_3_dfm_1[3]);
  assign xor_28_nl = xor_cse_20 ^ (crc32_dat_out_rsci_din[2]) ^ xor_cse_38 ^ xor_cse_39
      ^ xor_cse_40 ^ xor_cse_42 ^ (crc32_dat_out_rsci_din[8]) ^ (pix_chan2_rsci_idat_mxwt[24])
      ^ (pix_chan2_rsci_idat_mxwt[1]) ^ (pix_chan2_rsci_idat_mxwt[17]);
  assign mux1h_3_nl = MUX1HOT_s_1_3_2(xor_20_nl, xor_28_nl, (~ (crc32_dat_out_rsci_din[1])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_253_nl = mux1h_3_nl | or_tmp_15;
  assign xor_7_nl = xor_cse ^ xor_cse_1 ^ xor_cse_4 ^ xor_cse_8 ^ xor_cse_9 ^ (MCOL_qr_10_lpi_3_dfm_1[7])
      ^ (crc32_dat_out_rsci_din[16]) ^ (MCOL_qr_8_lpi_3_dfm_1[0]) ^ (MCOL_qr_10_lpi_3_dfm_1[0])
      ^ (MCOL_qr_8_lpi_3_dfm_1[1]) ^ (MCOL_qr_10_lpi_3_dfm_1[4]);
  assign xor_14_nl = xor_cse_20 ^ (pix_chan2_rsci_idat_mxwt[0]) ^ (pix_chan2_rsci_idat_mxwt[16])
      ^ (crc32_dat_out_rsci_din[20]) ^ (pix_chan2_rsci_idat_mxwt[26]) ^ xor_cse_8
      ^ xor_cse_23 ^ xor_cse_24 ^ (pix_chan2_rsci_idat_mxwt[8]) ^ (crc32_dat_out_rsci_din[3])
      ^ (crc32_dat_out_rsci_din[6]) ^ (crc32_dat_out_rsci_din[16]);
  assign mux1h_1_nl = MUX1HOT_s_1_3_2(xor_7_nl, xor_14_nl, (~ (crc32_dat_out_rsci_din[0])),
      {or_tmp_1 , or_tmp_2 , (fsm_output[5])});
  assign or_252_nl = mux1h_1_nl | or_tmp_15;
  assign nl_EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_rsci_inst_crc32_dat_out_rsci_dout_run
      = {or_283_nl , or_282_nl , or_281_nl , or_280_nl , or_279_nl , or_278_nl ,
      or_277_nl , or_276_nl , or_275_nl , or_274_nl , or_273_nl , or_272_nl , or_271_nl
      , or_270_nl , or_269_nl , or_268_nl , or_267_nl , or_266_nl , or_265_nl , or_264_nl
      , or_263_nl , or_262_nl , or_261_nl , or_260_nl , or_259_nl , or_258_nl , or_257_nl
      , or_256_nl , or_255_nl , or_254_nl , or_253_nl , or_252_nl};
  wire [33:0] nl_EdgeDetect_IP_EdgeDetect_MagAng_run_dat_out_rsci_inst_dat_out_rsci_idat;
  assign nl_EdgeDetect_IP_EdgeDetect_MagAng_run_dat_out_rsci_inst_dat_out_rsci_idat
      = {dat_out_rsci_idat_33 , dat_out_rsci_idat_32 , dat_out_rsci_idat_31_24 ,
      dat_out_rsci_idat_23_16 , dat_out_rsci_idat_15_8 , dat_out_rsci_idat_7_0};
  EdgeDetect_IP_EdgeDetect_MagAng_run_dx_chan_rsci EdgeDetect_IP_EdgeDetect_MagAng_run_dx_chan_rsci_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dx_chan_rsc_dat(dx_chan_rsc_dat),
      .dx_chan_rsc_vld(dx_chan_rsc_vld),
      .dx_chan_rsc_rdy(dx_chan_rsc_rdy),
      .run_wen(run_wen),
      .dx_chan_rsci_oswt(reg_pix_chan2_rsci_iswt0_cse),
      .dx_chan_rsci_wen_comp(dx_chan_rsci_wen_comp),
      .dx_chan_rsci_idat_mxwt(dx_chan_rsci_idat_mxwt)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_dy_chan_rsci EdgeDetect_IP_EdgeDetect_MagAng_run_dy_chan_rsci_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dy_chan_rsc_dat(dy_chan_rsc_dat),
      .dy_chan_rsc_vld(dy_chan_rsc_vld),
      .dy_chan_rsc_rdy(dy_chan_rsc_rdy),
      .run_wen(run_wen),
      .dy_chan_rsci_oswt(reg_pix_chan2_rsci_iswt0_cse),
      .dy_chan_rsci_wen_comp(dy_chan_rsci_wen_comp),
      .dy_chan_rsci_idat_mxwt(dy_chan_rsci_idat_mxwt)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_pix_chan2_rsci EdgeDetect_IP_EdgeDetect_MagAng_run_pix_chan2_rsci_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .pix_chan2_rsc_dat(pix_chan2_rsc_dat),
      .pix_chan2_rsc_vld(pix_chan2_rsc_vld),
      .pix_chan2_rsc_rdy(pix_chan2_rsc_rdy),
      .run_wen(run_wen),
      .pix_chan2_rsci_oswt(reg_pix_chan2_rsci_iswt0_cse),
      .pix_chan2_rsci_wen_comp(pix_chan2_rsci_wen_comp),
      .pix_chan2_rsci_idat_mxwt(pix_chan2_rsci_idat_mxwt)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_rsci EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_rsci_inst
      (
      .crc32_pix_in_rsc_zout(crc32_pix_in_rsc_zout),
      .crc32_pix_in_rsc_lzout(crc32_pix_in_rsc_lzout),
      .crc32_pix_in_rsc_zin(crc32_pix_in_rsc_zin),
      .run_wten(nl_EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_rsci_inst_run_wten),
      .crc32_pix_in_rsci_iswt0(or_244_rmff),
      .crc32_pix_in_rsci_din(crc32_pix_in_rsci_din),
      .crc32_pix_in_rsci_dout_run(nl_EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_rsci_inst_crc32_pix_in_rsci_dout_run[31:0])
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_rsci EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_rsci_inst
      (
      .crc32_dat_out_rsc_zout(crc32_dat_out_rsc_zout),
      .crc32_dat_out_rsc_lzout(crc32_dat_out_rsc_lzout),
      .crc32_dat_out_rsc_zin(crc32_dat_out_rsc_zin),
      .run_wten(nl_EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_rsci_inst_run_wten),
      .crc32_dat_out_rsci_iswt0(or_244_rmff),
      .crc32_dat_out_rsci_din(crc32_dat_out_rsci_din),
      .crc32_dat_out_rsci_dout_run(nl_EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_rsci_inst_crc32_dat_out_rsci_dout_run[31:0])
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_dat_out_rsci EdgeDetect_IP_EdgeDetect_MagAng_run_dat_out_rsci_inst
      (
      .dat_out_rsc_dat(dat_out_rsc_dat),
      .dat_out_rsc_vld(dat_out_rsc_vld),
      .dat_out_rsc_rdy(dat_out_rsc_rdy),
      .dat_out_rsci_oswt(reg_dat_out_rsci_iswt0_cse),
      .dat_out_rsci_wen_comp(dat_out_rsci_wen_comp),
      .dat_out_rsci_idat(nl_EdgeDetect_IP_EdgeDetect_MagAng_run_dat_out_rsci_inst_dat_out_rsci_idat[33:0])
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_sw_in_triosy_obj EdgeDetect_IP_EdgeDetect_MagAng_run_sw_in_triosy_obj_inst
      (
      .sw_in_triosy_lz(sw_in_triosy_lz),
      .run_wten(run_wten),
      .sw_in_triosy_obj_iswt0(reg_crc32_dat_out_triosy_obj_iswt0_cse)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_triosy_obj EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_pix_in_triosy_obj_inst
      (
      .crc32_pix_in_triosy_lz(crc32_pix_in_triosy_lz),
      .run_wten(run_wten),
      .crc32_pix_in_triosy_obj_iswt0(reg_crc32_dat_out_triosy_obj_iswt0_cse)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_triosy_obj EdgeDetect_IP_EdgeDetect_MagAng_run_crc32_dat_out_triosy_obj_inst
      (
      .crc32_dat_out_triosy_lz(crc32_dat_out_triosy_lz),
      .run_wten(run_wten),
      .crc32_dat_out_triosy_obj_iswt0(reg_crc32_dat_out_triosy_obj_iswt0_cse)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_staller EdgeDetect_IP_EdgeDetect_MagAng_run_staller_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .run_wen(run_wen),
      .run_wten(run_wten),
      .dx_chan_rsci_wen_comp(dx_chan_rsci_wen_comp),
      .dy_chan_rsci_wen_comp(dy_chan_rsci_wen_comp),
      .pix_chan2_rsci_wen_comp(pix_chan2_rsci_wen_comp),
      .dat_out_rsci_wen_comp(dat_out_rsci_wen_comp)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run_run_fsm EdgeDetect_IP_EdgeDetect_MagAng_run_run_fsm_inst
      (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .run_wen(run_wen),
      .fsm_output(fsm_output),
      .MCOL_C_1_tr0(MCOL_equal_2_tmp),
      .MROW_C_0_tr0(MROW_equal_tmp)
    );
  assign MCOL_and_cse = run_wen & (or_tmp_1 | or_tmp_2);
  assign MCOL_and_4_cse = run_wen & (fsm_output[3]);
  assign or_244_rmff = (fsm_output[6]) | (fsm_output[1]) | (fsm_output[3]) | and_484_cse;
  assign MROW_y_or_cse = (fsm_output[2]) | (fsm_output[5]);
  assign MCOL_qr_9_lpi_3_dfm_1 = MUX_v_8_2_2((abs_sum_1_sva_1[7:0]), 8'b11111111,
      (abs_sum_1_sva_1[8]));
  assign MCOL_qr_11_lpi_3_dfm_1 = MUX_v_8_2_2((abs_sum_3_sva_1[7:0]), 8'b11111111,
      (abs_sum_3_sva_1[8]));
  assign MCOL_qr_10_lpi_3_dfm_1 = MUX_v_8_2_2((abs_sum_2_sva_1[7:0]), 8'b11111111,
      (abs_sum_2_sva_1[8]));
  assign MCOL_qr_8_lpi_3_dfm_1 = MUX_v_8_2_2((abs_sum_0_sva_1[7:0]), 8'b11111111,
      (abs_sum_0_sva_1[8]));
  assign nl_MCOL_qif_2_acc_nl =  -(dx_chan_rsci_idat_mxwt[16:9]);
  assign MCOL_qif_2_acc_nl = nl_MCOL_qif_2_acc_nl[7:0];
  assign MCOL_mux_2_nl = MUX_v_8_2_2((dx_chan_rsci_idat_mxwt[16:9]), MCOL_qif_2_acc_nl,
      dx_chan_rsci_idat_mxwt[17]);
  assign nl_MCOL_qif_3_acc_nl =  -(dy_chan_rsci_idat_mxwt[16:9]);
  assign MCOL_qif_3_acc_nl = nl_MCOL_qif_3_acc_nl[7:0];
  assign MCOL_mux_3_nl = MUX_v_8_2_2((dy_chan_rsci_idat_mxwt[16:9]), MCOL_qif_3_acc_nl,
      dy_chan_rsci_idat_mxwt[17]);
  assign nl_abs_sum_1_sva_1 = conv_u2u_8_9(MCOL_mux_2_nl) + conv_u2u_8_9(MCOL_mux_3_nl);
  assign abs_sum_1_sva_1 = nl_abs_sum_1_sva_1[8:0];
  assign nl_MCOL_qif_4_acc_nl =  -(dx_chan_rsci_idat_mxwt[25:18]);
  assign MCOL_qif_4_acc_nl = nl_MCOL_qif_4_acc_nl[7:0];
  assign MCOL_mux_4_nl = MUX_v_8_2_2((dx_chan_rsci_idat_mxwt[25:18]), MCOL_qif_4_acc_nl,
      dx_chan_rsci_idat_mxwt[26]);
  assign nl_MCOL_qif_5_acc_nl =  -(dy_chan_rsci_idat_mxwt[25:18]);
  assign MCOL_qif_5_acc_nl = nl_MCOL_qif_5_acc_nl[7:0];
  assign MCOL_mux_5_nl = MUX_v_8_2_2((dy_chan_rsci_idat_mxwt[25:18]), MCOL_qif_5_acc_nl,
      dy_chan_rsci_idat_mxwt[26]);
  assign nl_abs_sum_2_sva_1 = conv_u2u_8_9(MCOL_mux_4_nl) + conv_u2u_8_9(MCOL_mux_5_nl);
  assign abs_sum_2_sva_1 = nl_abs_sum_2_sva_1[8:0];
  assign nl_MCOL_qif_6_acc_nl =  -(dx_chan_rsci_idat_mxwt[34:27]);
  assign MCOL_qif_6_acc_nl = nl_MCOL_qif_6_acc_nl[7:0];
  assign MCOL_mux_6_nl = MUX_v_8_2_2((dx_chan_rsci_idat_mxwt[34:27]), MCOL_qif_6_acc_nl,
      dx_chan_rsci_idat_mxwt[35]);
  assign nl_MCOL_qif_7_acc_nl =  -(dy_chan_rsci_idat_mxwt[34:27]);
  assign MCOL_qif_7_acc_nl = nl_MCOL_qif_7_acc_nl[7:0];
  assign MCOL_mux_7_nl = MUX_v_8_2_2((dy_chan_rsci_idat_mxwt[34:27]), MCOL_qif_7_acc_nl,
      dy_chan_rsci_idat_mxwt[35]);
  assign nl_abs_sum_3_sva_1 = conv_u2u_8_9(MCOL_mux_6_nl) + conv_u2u_8_9(MCOL_mux_7_nl);
  assign abs_sum_3_sva_1 = nl_abs_sum_3_sva_1[8:0];
  assign nl_MCOL_qif_acc_nl =  -(dx_chan_rsci_idat_mxwt[7:0]);
  assign MCOL_qif_acc_nl = nl_MCOL_qif_acc_nl[7:0];
  assign MCOL_mux_8_nl = MUX_v_8_2_2((dx_chan_rsci_idat_mxwt[7:0]), MCOL_qif_acc_nl,
      dx_chan_rsci_idat_mxwt[8]);
  assign nl_MCOL_qif_1_acc_nl =  -(dy_chan_rsci_idat_mxwt[7:0]);
  assign MCOL_qif_1_acc_nl = nl_MCOL_qif_1_acc_nl[7:0];
  assign MCOL_mux_9_nl = MUX_v_8_2_2((dy_chan_rsci_idat_mxwt[7:0]), MCOL_qif_1_acc_nl,
      dy_chan_rsci_idat_mxwt[8]);
  assign nl_abs_sum_0_sva_1 = conv_u2u_8_9(MCOL_mux_8_nl) + conv_u2u_8_9(MCOL_mux_9_nl);
  assign abs_sum_0_sva_1 = nl_abs_sum_0_sva_1[8:0];
  assign nl_operator_9_false_acc_nl = heightIn + 9'b111111111;
  assign operator_9_false_acc_nl = nl_operator_9_false_acc_nl[8:0];
  assign MROW_equal_tmp = MROW_y_sva == operator_9_false_acc_nl;
  assign nl_operator_11_true_acc_nl = conv_u2s_8_9(widthIn[9:2]) + 9'b111111111;
  assign operator_11_true_acc_nl = nl_operator_11_true_acc_nl[8:0];
  assign MCOL_equal_2_tmp = MCOL_x_sva == (signext_10_9(operator_11_true_acc_nl));
  assign or_tmp_1 = sw_in_rsci_idat & (fsm_output[3]);
  assign or_tmp_2 = (~ sw_in_rsci_idat) & (fsm_output[3]);
  assign or_tmp_15 = ~((fsm_output[3]) | (fsm_output[5]));
  assign and_484_cse = MROW_equal_tmp & (fsm_output[5]);
  assign xor_cse = (crc32_dat_out_rsci_din[23]) ^ (crc32_dat_out_rsci_din[1]) ^ (crc32_dat_out_rsci_din[7])
      ^ (crc32_dat_out_rsci_din[4]);
  assign xor_cse_1 = (crc32_dat_out_rsci_din[6]) ^ (MCOL_qr_8_lpi_3_dfm_1[6]) ^ (MCOL_qr_8_lpi_3_dfm_1[3])
      ^ (crc32_dat_out_rsci_din[3]);
  assign xor_cse_4 = (crc32_dat_out_rsci_din[8]) ^ (MCOL_qr_9_lpi_3_dfm_1[0]) ^ (MCOL_qr_8_lpi_3_dfm_1[2])
      ^ (MCOL_qr_8_lpi_3_dfm_1[4]);
  assign xor_cse_8 = (crc32_dat_out_rsci_din[22]) ^ (crc32_dat_out_rsci_din[2]) ^
      (crc32_dat_out_rsci_din[0]) ^ (crc32_dat_out_rsci_din[26]);
  assign xor_cse_9 = (MCOL_qr_8_lpi_3_dfm_1[7]) ^ (MCOL_qr_10_lpi_3_dfm_1[6]) ^ (MCOL_qr_11_lpi_3_dfm_1[2])
      ^ (crc32_dat_out_rsci_din[20]);
  assign xor_cse_20 = xor_cse ^ (pix_chan2_rsci_idat_mxwt[23]) ^ (pix_chan2_rsci_idat_mxwt[2]);
  assign xor_cse_23 = (pix_chan2_rsci_idat_mxwt[20]) ^ (pix_chan2_rsci_idat_mxwt[7])
      ^ (pix_chan2_rsci_idat_mxwt[3]) ^ (pix_chan2_rsci_idat_mxwt[22]);
  assign xor_cse_24 = (pix_chan2_rsci_idat_mxwt[1]) ^ (pix_chan2_rsci_idat_mxwt[4])
      ^ (crc32_dat_out_rsci_din[8]) ^ (pix_chan2_rsci_idat_mxwt[6]);
  assign xor_cse_26 = (crc32_dat_out_rsci_din[21]) ^ (MCOL_qr_10_lpi_3_dfm_1[5])
      ^ (MCOL_qr_8_lpi_3_dfm_1[3]) ^ (MCOL_qr_11_lpi_3_dfm_1[0]);
  assign xor_cse_29 = (crc32_dat_out_rsci_din[5]) ^ (MCOL_qr_8_lpi_3_dfm_1[5]) ^
      (crc32_dat_out_rsci_din[9]) ^ (MCOL_qr_9_lpi_3_dfm_1[1]);
  assign xor_cse_32 = (MCOL_qr_10_lpi_3_dfm_1[1]) ^ (MCOL_qr_8_lpi_3_dfm_1[1]) ^
      (MCOL_qr_8_lpi_3_dfm_1[7]) ^ (MCOL_qr_10_lpi_3_dfm_1[7]);
  assign xor_cse_38 = (pix_chan2_rsci_idat_mxwt[3]) ^ (pix_chan2_rsci_idat_mxwt[21])
      ^ (pix_chan2_rsci_idat_mxwt[8]) ^ (pix_chan2_rsci_idat_mxwt[7]);
  assign xor_cse_39 = (crc32_dat_out_rsci_din[5]) ^ (crc32_dat_out_rsci_din[3]) ^
      (pix_chan2_rsci_idat_mxwt[27]) ^ (crc32_dat_out_rsci_din[27]);
  assign xor_cse_40 = (crc32_dat_out_rsci_din[21]) ^ (crc32_dat_out_rsci_din[24])
      ^ (pix_chan2_rsci_idat_mxwt[4]) ^ (crc32_dat_out_rsci_din[17]);
  assign xor_cse_42 = (pix_chan2_rsci_idat_mxwt[9]) ^ (crc32_dat_out_rsci_din[9])
      ^ (pix_chan2_rsci_idat_mxwt[5]);
  assign xor_cse_45 = (crc32_dat_out_rsci_din[3]) ^ (crc32_dat_out_rsci_din[0]) ^
      (crc32_dat_out_rsci_din[28]) ^ (crc32_dat_out_rsci_din[9]);
  assign xor_cse_44 = xor_cse_45 ^ (MCOL_qr_8_lpi_3_dfm_1[3]) ^ (MCOL_qr_9_lpi_3_dfm_1[1]);
  assign xor_cse_47 = (crc32_dat_out_rsci_din[5]) ^ (MCOL_qr_8_lpi_3_dfm_1[5]) ^
      (MCOL_qr_8_lpi_3_dfm_1[0]) ^ (MCOL_qr_10_lpi_3_dfm_1[6]);
  assign xor_cse_48 = (crc32_dat_out_rsci_din[18]) ^ (MCOL_qr_10_lpi_3_dfm_1[2])
      ^ (MCOL_qr_11_lpi_3_dfm_1[1]) ^ (crc32_dat_out_rsci_din[25]);
  assign xor_cse_51 = (crc32_dat_out_rsci_din[6]) ^ (MCOL_qr_8_lpi_3_dfm_1[6]) ^
      (crc32_dat_out_rsci_din[24]) ^ (MCOL_qr_11_lpi_3_dfm_1[0]);
  assign xor_cse_57 = (pix_chan2_rsci_idat_mxwt[18]) ^ (pix_chan2_rsci_idat_mxwt[22])
      ^ (pix_chan2_rsci_idat_mxwt[0]) ^ (pix_chan2_rsci_idat_mxwt[5]);
  assign xor_cse_58 = (pix_chan2_rsci_idat_mxwt[24]) ^ (crc32_dat_out_rsci_din[24])
      ^ (pix_chan2_rsci_idat_mxwt[6]) ^ (crc32_dat_out_rsci_din[6]);
  assign xor_cse_59 = (pix_chan2_rsci_idat_mxwt[4]) ^ (pix_chan2_rsci_idat_mxwt[2])
      ^ (pix_chan2_rsci_idat_mxwt[9]) ^ (crc32_dat_out_rsci_din[5]);
  assign xor_cse_60 = (crc32_dat_out_rsci_din[8]) ^ (pix_chan2_rsci_idat_mxwt[10])
      ^ (crc32_dat_out_rsci_din[10]) ^ (pix_chan2_rsci_idat_mxwt[8]);
  assign xor_cse_65 = (crc32_dat_out_rsci_din[5]) ^ (MCOL_qr_8_lpi_3_dfm_1[5]) ^
      (MCOL_qr_11_lpi_3_dfm_1[1]) ^ (MCOL_qr_11_lpi_3_dfm_1[5]);
  assign xor_cse_63 = (crc32_dat_out_rsci_din[11]) ^ (MCOL_qr_9_lpi_3_dfm_1[3]) ^
      xor_cse_65;
  assign xor_cse_68 = (MCOL_qr_10_lpi_3_dfm_1[7]) ^ (MCOL_qr_8_lpi_3_dfm_1[1]) ^
      (MCOL_qr_9_lpi_3_dfm_1[2]) ^ (MCOL_qr_11_lpi_3_dfm_1[2]);
  assign xor_cse_69 = (MCOL_qr_8_lpi_3_dfm_1[7]) ^ (crc32_dat_out_rsci_din[9]) ^
      (MCOL_qr_9_lpi_3_dfm_1[1]) ^ (MCOL_qr_8_lpi_3_dfm_1[4]);
  assign xor_cse_71 = (crc32_dat_out_rsci_din[29]) ^ (crc32_dat_out_rsci_din[19])
      ^ (MCOL_qr_10_lpi_3_dfm_1[3]);
  assign xor_cse_75 = (pix_chan2_rsci_idat_mxwt[3]) ^ (pix_chan2_rsci_idat_mxwt[6])
      ^ (pix_chan2_rsci_idat_mxwt[5]) ^ (pix_chan2_rsci_idat_mxwt[19]);
  assign xor_cse_74 = xor_cse_75 ^ (crc32_dat_out_rsci_din[3]) ^ (crc32_dat_out_rsci_din[25]);
  assign xor_cse_77 = (pix_chan2_rsci_idat_mxwt[9]) ^ (crc32_dat_out_rsci_din[6])
      ^ (pix_chan2_rsci_idat_mxwt[26]) ^ (crc32_dat_out_rsci_din[9]);
  assign xor_cse_78 = (crc32_dat_out_rsci_din[10]) ^ (pix_chan2_rsci_idat_mxwt[10])
      ^ (pix_chan2_rsci_idat_mxwt[25]) ^ (crc32_dat_out_rsci_din[11]);
  assign xor_cse_79 = (pix_chan2_rsci_idat_mxwt[1]) ^ (pix_chan2_rsci_idat_mxwt[23])
      ^ (pix_chan2_rsci_idat_mxwt[11]) ^ (crc32_dat_out_rsci_din[26]);
  assign xor_cse_81 = (pix_chan2_rsci_idat_mxwt[29]) ^ (pix_chan2_rsci_idat_mxwt[7])
      ^ (crc32_dat_out_rsci_din[29]);
  assign xor_cse_84 = (crc32_dat_out_rsci_din[27]) ^ (MCOL_qr_11_lpi_3_dfm_1[3])
      ^ (MCOL_qr_8_lpi_3_dfm_1[7]) ^ (crc32_dat_out_rsci_din[11]);
  assign xor_cse_85 = (crc32_dat_out_rsci_din[7]) ^ (crc32_dat_out_rsci_din[2]) ^
      (crc32_dat_out_rsci_din[26]) ^ (crc32_dat_out_rsci_din[10]);
  assign xor_cse_83 = xor_cse_84 ^ (MCOL_qr_11_lpi_3_dfm_1[2]) ^ (crc32_dat_out_rsci_din[30])
      ^ xor_cse_85;
  assign xor_cse_88 = (crc32_dat_out_rsci_din[6]) ^ (MCOL_qr_8_lpi_3_dfm_1[6]) ^
      (MCOL_qr_9_lpi_3_dfm_1[3]) ^ (MCOL_qr_10_lpi_3_dfm_1[4]);
  assign xor_cse_89 = (crc32_dat_out_rsci_din[12]) ^ (MCOL_qr_9_lpi_3_dfm_1[4]) ^
      (MCOL_qr_11_lpi_3_dfm_1[6]) ^ (MCOL_qr_9_lpi_3_dfm_1[2]);
  assign xor_cse_94 = (pix_chan2_rsci_idat_mxwt[7]) ^ (pix_chan2_rsci_idat_mxwt[26])
      ^ (pix_chan2_rsci_idat_mxwt[10]) ^ (pix_chan2_rsci_idat_mxwt[27]);
  assign xor_cse_93 = xor_cse_94 ^ xor_cse_85 ^ (crc32_dat_out_rsci_din[11]) ^ (pix_chan2_rsci_idat_mxwt[11]);
  assign xor_cse_97 = (crc32_dat_out_rsci_din[5]) ^ (crc32_dat_out_rsci_din[8]) ^
      (pix_chan2_rsci_idat_mxwt[5]) ^ (crc32_dat_out_rsci_din[12]);
  assign xor_cse_98 = (crc32_dat_out_rsci_din[30]) ^ (crc32_dat_out_rsci_din[20])
      ^ (crc32_dat_out_rsci_din[27]) ^ (pix_chan2_rsci_idat_mxwt[2]);
  assign xor_cse_99 = (pix_chan2_rsci_idat_mxwt[20]) ^ (pix_chan2_rsci_idat_mxwt[12])
      ^ (pix_chan2_rsci_idat_mxwt[8]) ^ (crc32_dat_out_rsci_din[4]);
  assign xor_cse_100 = (crc32_dat_out_rsci_din[12]) ^ (MCOL_qr_9_lpi_3_dfm_1[4])
      ^ (MCOL_qr_11_lpi_3_dfm_1[4]) ^ (MCOL_qr_8_lpi_3_dfm_1[0]);
  assign xor_cse_101 = (crc32_dat_out_rsci_din[21]) ^ (MCOL_qr_10_lpi_3_dfm_1[5])
      ^ (MCOL_qr_9_lpi_3_dfm_1[1]) ^ (crc32_dat_out_rsci_din[8]);
  assign xor_cse_102 = (crc32_dat_out_rsci_din[7]) ^ (crc32_dat_out_rsci_din[31])
      ^ (crc32_dat_out_rsci_din[13]) ^ (crc32_dat_out_rsci_din[25]);
  assign xor_cse_103 = (MCOL_qr_9_lpi_3_dfm_1[0]) ^ (MCOL_qr_9_lpi_3_dfm_1[3]) ^
      (MCOL_qr_9_lpi_3_dfm_1[5]) ^ (crc32_dat_out_rsci_din[6]);
  assign xor_cse_109 = (pix_chan2_rsci_idat_mxwt[0]) ^ (pix_chan2_rsci_idat_mxwt[12])
      ^ (pix_chan2_rsci_idat_mxwt[13]) ^ (pix_chan2_rsci_idat_mxwt[6]);
  assign xor_cse_108 = (pix_chan2_rsci_idat_mxwt[27]) ^ xor_cse_38 ^ (pix_chan2_rsci_idat_mxwt[31])
      ^ xor_cse_109;
  assign xor_cse_112 = (pix_chan2_rsci_idat_mxwt[25]) ^ (pix_chan2_rsci_idat_mxwt[11])
      ^ (crc32_dat_out_rsci_din[11]) ^ (crc32_dat_out_rsci_din[27]);
  assign xor_cse_114 = (crc32_dat_out_rsci_din[2]) ^ (crc32_dat_out_rsci_din[20])
      ^ (crc32_dat_out_rsci_din[23]) ^ (crc32_dat_out_rsci_din[16]);
  assign xor_cse_115 = (MCOL_qr_10_lpi_3_dfm_1[7]) ^ (MCOL_qr_10_lpi_3_dfm_1[0])
      ^ (MCOL_qr_8_lpi_3_dfm_1[2]) ^ (crc32_dat_out_rsci_din[14]);
  assign xor_cse_117 = (crc32_dat_out_rsci_din[29]) ^ (crc32_dat_out_rsci_din[10])
      ^ (MCOL_qr_9_lpi_3_dfm_1[2]);
  assign xor_cse_120 = (pix_chan2_rsci_idat_mxwt[2]) ^ (pix_chan2_rsci_idat_mxwt[23])
      ^ (pix_chan2_rsci_idat_mxwt[16]) ^ (pix_chan2_rsci_idat_mxwt[28]);
  assign xor_cse_121 = (crc32_dat_out_rsci_din[14]) ^ (pix_chan2_rsci_idat_mxwt[14])
      ^ (crc32_dat_out_rsci_din[13]) ^ (pix_chan2_rsci_idat_mxwt[13]);
  assign xor_cse_122 = (pix_chan2_rsci_idat_mxwt[10]) ^ (crc32_dat_out_rsci_din[10])
      ^ (pix_chan2_rsci_idat_mxwt[3]) ^ (crc32_dat_out_rsci_din[29]);
  assign xor_cse_123 = (pix_chan2_rsci_idat_mxwt[20]) ^ (pix_chan2_rsci_idat_mxwt[29])
      ^ (pix_chan2_rsci_idat_mxwt[12]);
  assign xor_cse_125 = (crc32_dat_out_rsci_din[13]) ^ (MCOL_qr_9_lpi_3_dfm_1[5])
      ^ (MCOL_qr_11_lpi_3_dfm_1[5]) ^ (MCOL_qr_11_lpi_3_dfm_1[6]);
  assign xor_cse_126 = (crc32_dat_out_rsci_din[24]) ^ (crc32_dat_out_rsci_din[4])
      ^ (crc32_dat_out_rsci_din[30]) ^ (crc32_dat_out_rsci_din[3]);
  assign xor_cse_127 = (crc32_dat_out_rsci_din[14]) ^ (MCOL_qr_9_lpi_3_dfm_1[6])
      ^ (MCOL_qr_8_lpi_3_dfm_1[4]) ^ (crc32_dat_out_rsci_din[17]);
  assign xor_cse_131 = (pix_chan2_rsci_idat_mxwt[24]) ^ (pix_chan2_rsci_idat_mxwt[17])
      ^ (pix_chan2_rsci_idat_mxwt[29]) ^ (pix_chan2_rsci_idat_mxwt[30]);
  assign xor_cse_132 = (pix_chan2_rsci_idat_mxwt[4]) ^ (pix_chan2_rsci_idat_mxwt[11])
      ^ (crc32_dat_out_rsci_din[11]) ^ (pix_chan2_rsci_idat_mxwt[15]);
  assign xor_cse_133 = (pix_chan2_rsci_idat_mxwt[1]) ^ (pix_chan2_rsci_idat_mxwt[21])
      ^ (crc32_dat_out_rsci_din[1]) ^ (crc32_dat_out_rsci_din[21]);
  assign xor_cse_135 = (crc32_dat_out_rsci_din[0]) ^ (crc32_dat_out_rsci_din[22])
      ^ (crc32_dat_out_rsci_din[4]) ^ (crc32_dat_out_rsci_din[30]);
  assign xor_cse_136 = (crc32_dat_out_rsci_din[14]) ^ (MCOL_qr_9_lpi_3_dfm_1[6])
      ^ (MCOL_qr_11_lpi_3_dfm_1[7]) ^ (crc32_dat_out_rsci_din[31]);
  assign xor_cse_137 = (crc32_dat_out_rsci_din[15]) ^ (MCOL_qr_9_lpi_3_dfm_1[7])
      ^ (MCOL_qr_8_lpi_3_dfm_1[2]) ^ (MCOL_qr_10_lpi_3_dfm_1[0]);
  assign xor_cse_140 = (pix_chan2_rsci_idat_mxwt[16]) ^ (crc32_dat_out_rsci_din[16])
      ^ (crc32_dat_out_rsci_din[31]) ^ xor_cse_135;
  assign xor_cse_142 = (pix_chan2_rsci_idat_mxwt[2]) ^ (pix_chan2_rsci_idat_mxwt[12])
      ^ (pix_chan2_rsci_idat_mxwt[31]) ^ (crc32_dat_out_rsci_din[12]);
  assign xor_cse_144 = (pix_chan2_rsci_idat_mxwt[25]) ^ (crc32_dat_out_rsci_din[25])
      ^ (crc32_dat_out_rsci_din[18]) ^ (pix_chan2_rsci_idat_mxwt[30]);
  assign xor_cse_146 = xor_cse_47 ^ (MCOL_qr_10_lpi_3_dfm_1[1]) ^ (crc32_dat_out_rsci_din[12])
      ^ (MCOL_qr_9_lpi_3_dfm_1[4]);
  assign xor_cse_148 = (crc32_dat_out_rsci_din[7]) ^ (crc32_dat_out_rsci_din[19])
      ^ (crc32_dat_out_rsci_din[31]) ^ (crc32_dat_out_rsci_din[15]);
  assign xor_cse_149 = (crc32_dat_out_rsci_din[22]) ^ (crc32_dat_out_rsci_din[2])
      ^ (crc32_dat_out_rsci_din[0]) ^ (crc32_dat_out_rsci_din[17]);
  assign xor_cse_150 = (MCOL_qr_11_lpi_3_dfm_1[7]) ^ (MCOL_qr_10_lpi_3_dfm_1[3])
      ^ (MCOL_qr_9_lpi_3_dfm_1[7]) ^ (MCOL_qr_8_lpi_3_dfm_1[7]);
  assign xor_cse_152 = (crc32_dat_out_rsci_din[13]) ^ (MCOL_qr_9_lpi_3_dfm_1[5])
      ^ (crc32_dat_out_rsci_din[4]);
  assign xor_cse_154 = xor_cse_148 ^ (crc32_dat_out_rsci_din[20]) ^ (pix_chan2_rsci_idat_mxwt[4])
      ^ (pix_chan2_rsci_idat_mxwt[15]);
  assign xor_cse_156 = (pix_chan2_rsci_idat_mxwt[7]) ^ (pix_chan2_rsci_idat_mxwt[31])
      ^ (pix_chan2_rsci_idat_mxwt[0]) ^ (pix_chan2_rsci_idat_mxwt[22]);
  assign xor_cse_159 = (crc32_dat_out_rsci_din[18]) ^ (crc32_dat_out_rsci_din[7])
      ^ (MCOL_qr_10_lpi_3_dfm_1[2]) ^ (MCOL_qr_8_lpi_3_dfm_1[2]);
  assign xor_cse_161 = (pix_chan2_rsci_idat_mxwt[7]) ^ (crc32_dat_out_rsci_din[7])
      ^ (crc32_dat_out_rsci_din[18]) ^ (pix_chan2_rsci_idat_mxwt[26]);
  assign xor_cse_163 = (crc32_dat_out_rsci_din[27]) ^ (MCOL_qr_11_lpi_3_dfm_1[3])
      ^ (crc32_dat_out_rsci_din[19]) ^ (MCOL_qr_10_lpi_3_dfm_1[3]);
  assign xor_cse_164 = (crc32_dat_out_rsci_din[22]) ^ (crc32_dat_out_rsci_din[15])
      ^ (crc32_dat_out_rsci_din[23]) ^ (crc32_dat_out_rsci_din[1]);
  assign xor_cse_168 = (crc32_dat_out_rsci_din[27]) ^ (crc32_dat_out_rsci_din[19])
      ^ (crc32_dat_out_rsci_din[1]) ^ (pix_chan2_rsci_idat_mxwt[1]);
  assign xor_cse_169 = (pix_chan2_rsci_idat_mxwt[23]) ^ (pix_chan2_rsci_idat_mxwt[14])
      ^ (crc32_dat_out_rsci_din[23]) ^ (crc32_dat_out_rsci_din[14]);
  assign xor_cse_170 = (pix_chan2_rsci_idat_mxwt[15]) ^ (crc32_dat_out_rsci_din[5])
      ^ (crc32_dat_out_rsci_din[22]) ^ (crc32_dat_out_rsci_din[6]);
  assign xor_cse_172 = (crc32_dat_out_rsci_din[24]) ^ (MCOL_qr_11_lpi_3_dfm_1[0])
      ^ (crc32_dat_out_rsci_din[28]) ^ (MCOL_qr_11_lpi_3_dfm_1[4]);
  assign xor_cse_174 = xor_cse_114 ^ xor_cse_120 ^ (pix_chan2_rsci_idat_mxwt[20])
      ^ (crc32_dat_out_rsci_din[28]);
  assign xor_cse_179 = (crc32_dat_out_rsci_din[25]) ^ (crc32_dat_out_rsci_din[29])
      ^ (crc32_dat_out_rsci_din[24]) ^ (crc32_dat_out_rsci_din[17]);
  assign xor_cse_178 = (crc32_dat_out_rsci_din[0]) ^ (crc32_dat_out_rsci_din[3])
      ^ xor_cse_179;
  assign xor_cse_182 = (crc32_dat_out_rsci_din[10]) ^ (crc32_dat_out_rsci_din[16])
      ^ (crc32_dat_out_rsci_din[7]) ^ (MCOL_qr_9_lpi_3_dfm_1[2]);
  assign xor_cse_183 = (MCOL_qr_10_lpi_3_dfm_1[1]) ^ (crc32_dat_out_rsci_din[12])
      ^ (MCOL_qr_9_lpi_3_dfm_1[4]) ^ (crc32_dat_out_rsci_din[8]);
  assign xor_cse_185 = (pix_chan2_rsci_idat_mxwt[10]) ^ (crc32_dat_out_rsci_din[10])
      ^ (pix_chan2_rsci_idat_mxwt[29]) ^ (crc32_dat_out_rsci_din[7]);
  assign xor_cse_187 = (pix_chan2_rsci_idat_mxwt[17]) ^ (pix_chan2_rsci_idat_mxwt[0])
      ^ (pix_chan2_rsci_idat_mxwt[25]);
  assign xor_cse_189 = xor_cse_135 ^ (MCOL_qr_8_lpi_3_dfm_1[4]) ^ xor_cse_48 ^ (MCOL_qr_11_lpi_3_dfm_1[2]);
  assign xor_cse_192 = (MCOL_qr_10_lpi_3_dfm_1[1]) ^ (MCOL_qr_9_lpi_3_dfm_1[1]) ^
      (crc32_dat_out_rsci_din[9]) ^ (crc32_dat_out_rsci_din[11]);
  assign xor_cse_193 = (crc32_dat_out_rsci_din[1]) ^ (MCOL_qr_8_lpi_3_dfm_1[1]) ^
      (MCOL_qr_10_lpi_3_dfm_1[6]) ^ (crc32_dat_out_rsci_din[26]);
  assign xor_cse_195 = (pix_chan2_rsci_idat_mxwt[22]) ^ (pix_chan2_rsci_idat_mxwt[13])
      ^ (pix_chan2_rsci_idat_mxwt[18]) ^ (pix_chan2_rsci_idat_mxwt[8]);
  assign xor_cse_201 = (crc32_dat_out_rsci_din[26]) ^ (crc32_dat_out_rsci_din[13])
      ^ (crc32_dat_out_rsci_din[19]) ^ (crc32_dat_out_rsci_din[22]);
  assign xor_cse_202 = (MCOL_qr_9_lpi_3_dfm_1[3]) ^ (MCOL_qr_9_lpi_3_dfm_1[7]) ^
      (MCOL_qr_10_lpi_3_dfm_1[3]) ^ (crc32_dat_out_rsci_din[16]);
  assign xor_cse_205 = (pix_chan2_rsci_idat_mxwt[16]) ^ (crc32_dat_out_rsci_din[16])
      ^ (crc32_dat_out_rsci_din[28]) ^ (pix_chan2_rsci_idat_mxwt[28]);
  assign xor_cse_206 = (pix_chan2_rsci_idat_mxwt[24]) ^ (crc32_dat_out_rsci_din[24])
      ^ (crc32_dat_out_rsci_din[15]);
  assign xor_cse_211 = (MCOL_qr_10_lpi_3_dfm_1[4]) ^ (MCOL_qr_9_lpi_3_dfm_1[6]) ^
      (MCOL_qr_11_lpi_3_dfm_1[0]);
  assign xor_cse_215 = (pix_chan2_rsci_idat_mxwt[24]) ^ (pix_chan2_rsci_idat_mxwt[17])
      ^ (pix_chan2_rsci_idat_mxwt[29]) ^ (pix_chan2_rsci_idat_mxwt[14]);
  assign xor_cse_216 = xor_cse_179 ^ (crc32_dat_out_rsci_din[30]) ^ (MCOL_qr_9_lpi_3_dfm_1[7])
      ^ (MCOL_qr_11_lpi_3_dfm_1[1]);
  assign xor_cse_219 = (crc32_dat_out_rsci_din[18]) ^ (MCOL_qr_10_lpi_3_dfm_1[2])
      ^ (MCOL_qr_11_lpi_3_dfm_1[2]) ^ (crc32_dat_out_rsci_din[15]);
  assign xor_cse_221 = xor_cse_131 ^ xor_cse_109 ^ (crc32_dat_out_rsci_din[12]) ^
      (crc32_dat_out_rsci_din[13]);
  assign xor_cse_223 = (crc32_dat_out_rsci_din[21]) ^ (pix_chan2_rsci_idat_mxwt[28])
      ^ (pix_chan2_rsci_idat_mxwt[21]) ^ (pix_chan2_rsci_idat_mxwt[3]);
  assign xor_cse_222 = xor_cse_45 ^ (pix_chan2_rsci_idat_mxwt[9]) ^ xor_cse_223;
  assign xor_cse_225 = (pix_chan2_rsci_idat_mxwt[18]) ^ (crc32_dat_out_rsci_din[18])
      ^ (pix_chan2_rsci_idat_mxwt[15]) ^ (pix_chan2_rsci_idat_mxwt[25]);
  assign xor_cse_234 = (MCOL_qr_10_lpi_3_dfm_1[0]) ^ (crc32_dat_out_rsci_din[28])
      ^ (MCOL_qr_11_lpi_3_dfm_1[7]);
  assign xor_cse_240 = (crc32_dat_out_rsci_din[29]) ^ (crc32_dat_out_rsci_din[28])
      ^ (crc32_dat_out_rsci_din[31]) ^ (crc32_dat_out_rsci_din[3]);
  assign xor_cse_245 = (crc32_dat_out_rsci_din[2]) ^ (crc32_dat_out_rsci_din[8])
      ^ (crc32_dat_out_rsci_din[29]);
  assign xor_cse_248 = (crc32_dat_out_rsci_din[30]) ^ (crc32_dat_out_rsci_din[20])
      ^ (crc32_dat_out_rsci_din[23]) ^ (MCOL_qr_11_lpi_3_dfm_1[6]);
  assign xor_cse_253 = (pix_chan2_rsci_idat_mxwt[20]) ^ (pix_chan2_rsci_idat_mxwt[27])
      ^ (pix_chan2_rsci_idat_mxwt[19]) ^ (pix_chan2_rsci_idat_mxwt[31]);
  assign xor_cse_254 = (crc32_dat_out_rsci_din[30]) ^ (crc32_dat_out_rsci_din[31])
      ^ (crc32_dat_out_rsci_din[27]);
  assign xor_cse_256 = (crc32_dat_out_rsci_din[29]) ^ (MCOL_qr_10_lpi_3_dfm_1[7])
      ^ (crc32_dat_out_rsci_din[16]) ^ (crc32_dat_out_rsci_din[23]);
  assign xor_cse_259 = (pix_chan2_rsci_idat_mxwt[31]) ^ xor_cse_38 ^ (pix_chan2_rsci_idat_mxwt[6])
      ^ (pix_chan2_rsci_idat_mxwt[15]);
  assign xor_cse_264 = (crc32_dat_out_rsci_din[1]) ^ (crc32_dat_out_rsci_din[2])
      ^ (MCOL_qr_11_lpi_3_dfm_1[1]) ^ (MCOL_qr_8_lpi_3_dfm_1[2]);
  assign xor_cse_267 = (pix_chan2_rsci_idat_mxwt[27]) ^ (pix_chan2_rsci_idat_mxwt[20])
      ^ (pix_chan2_rsci_idat_mxwt[6]);
  assign xor_cse_292 = (pix_chan2_rsci_idat_mxwt[18]) ^ (pix_chan2_rsci_idat_mxwt[19])
      ^ (pix_chan2_rsci_idat_mxwt[14]) ^ (pix_chan2_rsci_idat_mxwt[31]);
  assign xor_cse_293 = (pix_chan2_rsci_idat_mxwt[4]) ^ (crc32_pix_in_rsci_din[4])
      ^ (crc32_pix_in_rsci_din[22]) ^ (crc32_pix_in_rsci_din[0]);
  assign xor_cse_294 = (pix_chan2_rsci_idat_mxwt[1]) ^ (crc32_pix_in_rsci_din[1])
      ^ (crc32_pix_in_rsci_din[23]) ^ (pix_chan2_rsci_idat_mxwt[23]);
  assign xor_cse_295 = (pix_chan2_rsci_idat_mxwt[20]) ^ (pix_chan2_rsci_idat_mxwt[8])
      ^ (pix_chan2_rsci_idat_mxwt[2]) ^ (crc32_pix_in_rsci_din[8]);
  assign xor_cse_296 = (pix_chan2_rsci_idat_mxwt[16]) ^ (crc32_pix_in_rsci_din[16])
      ^ (pix_chan2_rsci_idat_mxwt[22]) ^ (crc32_pix_in_rsci_din[6]);
  assign xor_cse_297 = (pix_chan2_rsci_idat_mxwt[26]) ^ (crc32_pix_in_rsci_din[26])
      ^ (pix_chan2_rsci_idat_mxwt[7]);
  assign xor_cse_300 = (pix_chan2_rsci_idat_mxwt[9]) ^ (crc32_pix_in_rsci_din[9])
      ^ (crc32_pix_in_rsci_din[5]) ^ (crc32_pix_in_rsci_din[3]);
  assign xor_cse_301 = (pix_chan2_rsci_idat_mxwt[24]) ^ (crc32_pix_in_rsci_din[7])
      ^ (crc32_pix_in_rsci_din[24]) ^ (crc32_pix_in_rsci_din[4]);
  assign xor_cse_302 = (pix_chan2_rsci_idat_mxwt[17]) ^ (crc32_pix_in_rsci_din[17])
      ^ (crc32_pix_in_rsci_din[2]) ^ (pix_chan2_rsci_idat_mxwt[2]);
  assign xor_cse_305 = xor_cse_293 ^ xor_cse_57 ^ (pix_chan2_rsci_idat_mxwt[25])
      ^ (crc32_pix_in_rsci_din[2]) ^ (pix_chan2_rsci_idat_mxwt[2]) ^ (crc32_pix_in_rsci_din[18])
      ^ (crc32_pix_in_rsci_din[25]);
  assign xor_cse_308 = (pix_chan2_rsci_idat_mxwt[9]) ^ (crc32_pix_in_rsci_din[9])
      ^ (crc32_pix_in_rsci_din[6]) ^ (crc32_pix_in_rsci_din[24]);
  assign xor_cse_309 = (crc32_pix_in_rsci_din[3]) ^ (crc32_pix_in_rsci_din[28]) ^
      (pix_chan2_rsci_idat_mxwt[28]) ^ (pix_chan2_rsci_idat_mxwt[3]);
  assign xor_cse_312 = (pix_chan2_rsci_idat_mxwt[26]) ^ (crc32_pix_in_rsci_din[26])
      ^ (crc32_pix_in_rsci_din[29]) ^ (pix_chan2_rsci_idat_mxwt[29]);
  assign xor_cse_313 = (pix_chan2_rsci_idat_mxwt[10]) ^ (crc32_pix_in_rsci_din[10])
      ^ (crc32_pix_in_rsci_din[11]) ^ (pix_chan2_rsci_idat_mxwt[11]);
  assign xor_cse_316 = (pix_chan2_rsci_idat_mxwt[11]) ^ (crc32_pix_in_rsci_din[11])
      ^ (crc32_pix_in_rsci_din[27]) ^ (crc32_pix_in_rsci_din[2]);
  assign xor_cse_317 = (crc32_pix_in_rsci_din[5]) ^ (pix_chan2_rsci_idat_mxwt[5])
      ^ (crc32_pix_in_rsci_din[12]) ^ (pix_chan2_rsci_idat_mxwt[12]);
  assign xor_cse_318 = (crc32_pix_in_rsci_din[26]) ^ (pix_chan2_rsci_idat_mxwt[6])
      ^ (crc32_pix_in_rsci_din[30]) ^ (crc32_pix_in_rsci_din[6]);
  assign xor_cse_321 = (pix_chan2_rsci_idat_mxwt[25]) ^ (crc32_pix_in_rsci_din[25])
      ^ (crc32_pix_in_rsci_din[7]) ^ (crc32_pix_in_rsci_din[31]);
  assign xor_cse_320 = xor_cse_321 ^ (crc32_pix_in_rsci_din[0]) ^ (crc32_pix_in_rsci_din[21]);
  assign xor_cse_323 = (pix_chan2_rsci_idat_mxwt[11]) ^ (crc32_pix_in_rsci_din[11])
      ^ (crc32_pix_in_rsci_din[6]) ^ (crc32_pix_in_rsci_din[27]);
  assign xor_cse_324 = (crc32_pix_in_rsci_din[28]) ^ (pix_chan2_rsci_idat_mxwt[28])
      ^ (crc32_pix_in_rsci_din[13]);
  assign xor_cse_326 = (crc32_pix_in_rsci_din[13]) ^ (pix_chan2_rsci_idat_mxwt[13])
      ^ (crc32_pix_in_rsci_din[14]) ^ (pix_chan2_rsci_idat_mxwt[14]);
  assign xor_cse_327 = (pix_chan2_rsci_idat_mxwt[10]) ^ (crc32_pix_in_rsci_din[10])
      ^ (crc32_pix_in_rsci_din[3]) ^ (crc32_pix_in_rsci_din[16]);
  assign xor_cse_328 = (crc32_pix_in_rsci_din[20]) ^ (crc32_pix_in_rsci_din[23])
      ^ (crc32_pix_in_rsci_din[28]) ^ (crc32_pix_in_rsci_din[12]);
  assign xor_cse_329 = (pix_chan2_rsci_idat_mxwt[0]) ^ (pix_chan2_rsci_idat_mxwt[9])
      ^ (crc32_pix_in_rsci_din[9]) ^ (crc32_pix_in_rsci_din[0]);
  assign xor_cse_331 = xor_cse_131 ^ (crc32_pix_in_rsci_din[29]) ^ (crc32_pix_in_rsci_din[17])
      ^ (crc32_pix_in_rsci_din[30]);
  assign xor_cse_334 = (pix_chan2_rsci_idat_mxwt[15]) ^ (crc32_pix_in_rsci_din[15])
      ^ (crc32_pix_in_rsci_din[3]) ^ (crc32_pix_in_rsci_din[1]);
  assign xor_cse_337 = (pix_chan2_rsci_idat_mxwt[14]) ^ (crc32_pix_in_rsci_din[14])
      ^ (crc32_pix_in_rsci_din[30]) ^ (pix_chan2_rsci_idat_mxwt[30]);
  assign xor_cse_338 = (pix_chan2_rsci_idat_mxwt[15]) ^ (crc32_pix_in_rsci_din[15])
      ^ (crc32_pix_in_rsci_din[5]) ^ (crc32_pix_in_rsci_din[31]);
  assign xor_cse_341 = xor_cse_156 ^ (pix_chan2_rsci_idat_mxwt[17]) ^ (crc32_pix_in_rsci_din[17])
      ^ (crc32_pix_in_rsci_din[19]);
  assign xor_cse_343 = (crc32_pix_in_rsci_din[20]) ^ (crc32_pix_in_rsci_din[2]) ^
      (crc32_pix_in_rsci_din[7]) ^ (pix_chan2_rsci_idat_mxwt[13]);
  assign xor_cse_345 = (pix_chan2_rsci_idat_mxwt[15]) ^ (crc32_pix_in_rsci_din[15])
      ^ (crc32_pix_in_rsci_din[13]);
  assign xor_cse_347 = (pix_chan2_rsci_idat_mxwt[2]) ^ (crc32_pix_in_rsci_din[18])
      ^ (crc32_pix_in_rsci_din[2]) ^ (crc32_pix_in_rsci_din[7]);
  assign xor_cse_349 = xor_cse_294 ^ (crc32_pix_in_rsci_din[10]) ^ (pix_chan2_rsci_idat_mxwt[10]);
  assign xor_cse_352 = (pix_chan2_rsci_idat_mxwt[27]) ^ (crc32_pix_in_rsci_din[8])
      ^ (pix_chan2_rsci_idat_mxwt[8]) ^ (crc32_pix_in_rsci_din[14]);
  assign xor_cse_353 = (crc32_pix_in_rsci_din[19]) ^ (crc32_pix_in_rsci_din[6]) ^
      (crc32_pix_in_rsci_din[5]) ^ (crc32_pix_in_rsci_din[22]);
  assign xor_cse_355 = xor_cse_120 ^ (pix_chan2_rsci_idat_mxwt[20]) ^ (crc32_pix_in_rsci_din[20])
      ^ (crc32_pix_in_rsci_din[23]);
  assign xor_cse_358 = (pix_chan2_rsci_idat_mxwt[24]) ^ (pix_chan2_rsci_idat_mxwt[4])
      ^ (crc32_pix_in_rsci_din[4]) ^ (crc32_pix_in_rsci_din[15]);
  assign xor_cse_359 = (pix_chan2_rsci_idat_mxwt[11]) ^ (crc32_pix_in_rsci_din[11])
      ^ (crc32_pix_in_rsci_din[7]) ^ (pix_chan2_rsci_idat_mxwt[15]);
  assign xor_cse_360 = (pix_chan2_rsci_idat_mxwt[25]) ^ (crc32_pix_in_rsci_din[25])
      ^ (crc32_pix_in_rsci_din[17]) ^ (crc32_pix_in_rsci_din[29]);
  assign xor_cse_361 = (crc32_pix_in_rsci_din[21]) ^ (crc32_pix_in_rsci_din[8]) ^
      (crc32_pix_in_rsci_din[7]) ^ (pix_chan2_rsci_idat_mxwt[24]);
  assign xor_cse_367 = (crc32_pix_in_rsci_din[26]) ^ xor_cse_94 ^ (crc32_pix_in_rsci_din[10]);
  assign xor_cse_372 = (crc32_pix_in_rsci_din[19]) ^ (pix_chan2_rsci_idat_mxwt[19])
      ^ (crc32_pix_in_rsci_din[27]) ^ (crc32_pix_in_rsci_din[13]);
  assign xor_cse_373 = (pix_chan2_rsci_idat_mxwt[16]) ^ (crc32_pix_in_rsci_din[16])
      ^ (pix_chan2_rsci_idat_mxwt[13]) ^ (crc32_pix_in_rsci_din[10]);
  assign xor_cse_379 = (crc32_pix_in_rsci_din[21]) ^ (pix_chan2_rsci_idat_mxwt[21])
      ^ (crc32_pix_in_rsci_din[30]) ^ (crc32_pix_in_rsci_din[12]);
  assign xor_cse_381 = (pix_chan2_rsci_idat_mxwt[27]) ^ (pix_chan2_rsci_idat_mxwt[18])
      ^ (crc32_pix_in_rsci_din[18]);
  assign xor_cse_410 = (pix_chan2_rsci_idat_mxwt[18]) ^ (crc32_pix_in_rsci_din[18])
      ^ (pix_chan2_rsci_idat_mxwt[15]) ^ (crc32_pix_in_rsci_din[24]);
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      dat_out_rsci_idat_7_0 <= 8'b00000000;
      dat_out_rsci_idat_15_8 <= 8'b00000000;
      dat_out_rsci_idat_23_16 <= 8'b00000000;
      dat_out_rsci_idat_31_24 <= 8'b00000000;
    end
    else if ( rst ) begin
      dat_out_rsci_idat_7_0 <= 8'b00000000;
      dat_out_rsci_idat_15_8 <= 8'b00000000;
      dat_out_rsci_idat_23_16 <= 8'b00000000;
      dat_out_rsci_idat_31_24 <= 8'b00000000;
    end
    else if ( MCOL_and_cse ) begin
      dat_out_rsci_idat_7_0 <= MUX_v_8_2_2(MCOL_qr_8_lpi_3_dfm_1, (pix_chan2_rsci_idat_mxwt[7:0]),
          or_tmp_2);
      dat_out_rsci_idat_15_8 <= MUX_v_8_2_2(MCOL_qr_9_lpi_3_dfm_1, (pix_chan2_rsci_idat_mxwt[15:8]),
          or_tmp_2);
      dat_out_rsci_idat_23_16 <= MUX_v_8_2_2(MCOL_qr_10_lpi_3_dfm_1, (pix_chan2_rsci_idat_mxwt[23:16]),
          or_tmp_2);
      dat_out_rsci_idat_31_24 <= MUX_v_8_2_2(MCOL_qr_11_lpi_3_dfm_1, (pix_chan2_rsci_idat_mxwt[31:24]),
          or_tmp_2);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      dat_out_rsci_idat_32 <= 1'b0;
      dat_out_rsci_idat_33 <= 1'b0;
    end
    else if ( rst ) begin
      dat_out_rsci_idat_32 <= 1'b0;
      dat_out_rsci_idat_33 <= 1'b0;
    end
    else if ( MCOL_and_4_cse ) begin
      dat_out_rsci_idat_32 <= ~((MROW_y_sva!=9'b000000000) | (MCOL_x_sva!=10'b0000000000));
      dat_out_rsci_idat_33 <= MCOL_x_sva == ({operator_10_false_acc_nl , (widthIn[1:0])});
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      reg_crc32_dat_out_triosy_obj_iswt0_cse <= 1'b0;
      reg_dat_out_rsci_iswt0_cse <= 1'b0;
      reg_pix_chan2_rsci_iswt0_cse <= 1'b0;
      MCOL_acc_4_itm <= 10'b0000000000;
    end
    else if ( rst ) begin
      reg_crc32_dat_out_triosy_obj_iswt0_cse <= 1'b0;
      reg_dat_out_rsci_iswt0_cse <= 1'b0;
      reg_pix_chan2_rsci_iswt0_cse <= 1'b0;
      MCOL_acc_4_itm <= 10'b0000000000;
    end
    else if ( run_wen ) begin
      reg_crc32_dat_out_triosy_obj_iswt0_cse <= and_484_cse;
      reg_dat_out_rsci_iswt0_cse <= fsm_output[3];
      reg_pix_chan2_rsci_iswt0_cse <= ((~ MROW_equal_tmp) & (fsm_output[5])) | (fsm_output[2])
          | ((~ MCOL_equal_2_tmp) & (fsm_output[4]));
      MCOL_acc_4_itm <= nl_MCOL_acc_4_itm[9:0];
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      MROW_y_sva <= 9'b000000000;
    end
    else if ( rst ) begin
      MROW_y_sva <= 9'b000000000;
    end
    else if ( run_wen & MROW_y_or_cse ) begin
      MROW_y_sva <= MUX_v_9_2_2(9'b000000000, MROW_acc_nl, MROW_y_not_1_nl);
    end
  end
  always @(posedge clk or negedge arst_n) begin
    if ( ~ arst_n ) begin
      MCOL_x_sva <= 10'b0000000000;
    end
    else if ( rst ) begin
      MCOL_x_sva <= 10'b0000000000;
    end
    else if ( run_wen & ((fsm_output[4]) | MROW_y_or_cse) ) begin
      MCOL_x_sva <= MUX_v_10_2_2(10'b0000000000, MCOL_acc_4_itm, MCOL_x_not_1_nl);
    end
  end
  assign nl_operator_10_false_acc_nl = (widthIn[9:2]) + 8'b11111111;
  assign operator_10_false_acc_nl = nl_operator_10_false_acc_nl[7:0];
  assign nl_MCOL_acc_4_itm  = MCOL_x_sva + 10'b0000000001;
  assign nl_MROW_acc_nl = MROW_y_sva + 9'b000000001;
  assign MROW_acc_nl = nl_MROW_acc_nl[8:0];
  assign MROW_y_not_1_nl = ~ (fsm_output[2]);
  assign MCOL_x_not_1_nl = ~ MROW_y_or_cse;

  function automatic  MUX1HOT_s_1_3_2;
    input  input_2;
    input  input_1;
    input  input_0;
    input [2:0] sel;
    reg  result;
  begin
    result = input_0 & sel[0];
    result = result | (input_1 & sel[1]);
    result = result | (input_2 & sel[2]);
    MUX1HOT_s_1_3_2 = result;
  end
  endfunction


  function automatic  MUX_s_1_2_2;
    input  input_0;
    input  input_1;
    input  sel;
    reg  result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_s_1_2_2 = result;
  end
  endfunction


  function automatic [9:0] MUX_v_10_2_2;
    input [9:0] input_0;
    input [9:0] input_1;
    input  sel;
    reg [9:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_10_2_2 = result;
  end
  endfunction


  function automatic [7:0] MUX_v_8_2_2;
    input [7:0] input_0;
    input [7:0] input_1;
    input  sel;
    reg [7:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_8_2_2 = result;
  end
  endfunction


  function automatic [8:0] MUX_v_9_2_2;
    input [8:0] input_0;
    input [8:0] input_1;
    input  sel;
    reg [8:0] result;
  begin
    case (sel)
      1'b0 : begin
        result = input_0;
      end
      default : begin
        result = input_1;
      end
    endcase
    MUX_v_9_2_2 = result;
  end
  endfunction


  function automatic [9:0] signext_10_9;
    input [8:0] vector;
  begin
    signext_10_9= {{1{vector[8]}}, vector};
  end
  endfunction


  function automatic [8:0] conv_u2s_8_9 ;
    input [7:0]  vector ;
  begin
    conv_u2s_8_9 =  {1'b0, vector};
  end
  endfunction


  function automatic [8:0] conv_u2u_8_9 ;
    input [7:0]  vector ;
  begin
    conv_u2u_8_9 = {1'b0, vector};
  end
  endfunction

endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_VerDer
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_VerDer (
  clk, rst, arst_n, dat_in_rsc_dat, dat_in_rsc_vld, dat_in_rsc_rdy, widthIn, heightIn,
      pix_chan1_rsc_dat, pix_chan1_rsc_vld, pix_chan1_rsc_rdy, dy_chan_rsc_dat, dy_chan_rsc_vld,
      dy_chan_rsc_rdy, line_buf0_rsc_clken, line_buf0_rsc_q, line_buf0_rsc_re, line_buf0_rsc_radr,
      line_buf0_rsc_we, line_buf0_rsc_d, line_buf0_rsc_wadr, line_buf1_rsc_clken,
      line_buf1_rsc_q, line_buf1_rsc_re, line_buf1_rsc_radr, line_buf1_rsc_we, line_buf1_rsc_d,
      line_buf1_rsc_wadr
);
  input clk;
  input rst;
  input arst_n;
  input [33:0] dat_in_rsc_dat;
  input dat_in_rsc_vld;
  output dat_in_rsc_rdy;
  input [9:0] widthIn;
  input [8:0] heightIn;
  output [31:0] pix_chan1_rsc_dat;
  output pix_chan1_rsc_vld;
  input pix_chan1_rsc_rdy;
  output [35:0] dy_chan_rsc_dat;
  output dy_chan_rsc_vld;
  input dy_chan_rsc_rdy;
  output line_buf0_rsc_clken;
  input [63:0] line_buf0_rsc_q;
  output line_buf0_rsc_re;
  output [6:0] line_buf0_rsc_radr;
  output line_buf0_rsc_we;
  output [63:0] line_buf0_rsc_d;
  output [6:0] line_buf0_rsc_wadr;
  output line_buf1_rsc_clken;
  input [63:0] line_buf1_rsc_q;
  output line_buf1_rsc_re;
  output [6:0] line_buf1_rsc_radr;
  output line_buf1_rsc_we;
  output [63:0] line_buf1_rsc_d;
  output [6:0] line_buf1_rsc_wadr;


  // Interconnect Declarations
  wire [63:0] line_buf0_rsci_d_d;
  wire [63:0] line_buf0_rsci_q_d;
  wire [6:0] line_buf0_rsci_radr_d;
  wire [6:0] line_buf0_rsci_wadr_d;
  wire [63:0] line_buf1_rsci_d_d;
  wire [63:0] line_buf1_rsci_q_d;
  wire [6:0] line_buf1_rsci_radr_d;
  wire [6:0] line_buf1_rsci_wadr_d;
  wire line_buf0_rsci_re_d_iff;
  wire line_buf0_rsci_we_d_iff;
  wire line_buf1_rsci_re_d_iff;
  wire line_buf1_rsci_we_d_iff;


  // Interconnect Declarations for Component Instantiations 
  EdgeDetect_IP_EdgeDetect_VerDer_Xilinx_RAMS_BLOCK_1R1W_RBW_rwport_en_6_7_64_80_1_80_64_1_gen
      line_buf0_rsci (
      .clken(line_buf0_rsc_clken),
      .q(line_buf0_rsc_q),
      .re(line_buf0_rsc_re),
      .radr(line_buf0_rsc_radr),
      .we(line_buf0_rsc_we),
      .d(line_buf0_rsc_d),
      .wadr(line_buf0_rsc_wadr),
      .clken_d(1'b1),
      .d_d(line_buf0_rsci_d_d),
      .q_d(line_buf0_rsci_q_d),
      .radr_d(line_buf0_rsci_radr_d),
      .re_d(line_buf0_rsci_re_d_iff),
      .wadr_d(line_buf0_rsci_wadr_d),
      .we_d(line_buf0_rsci_we_d_iff),
      .writeA_w_ram_ir_internal_WMASK_B_d(line_buf0_rsci_we_d_iff),
      .readA_r_ram_ir_internal_RMASK_B_d(line_buf0_rsci_re_d_iff)
    );
  EdgeDetect_IP_EdgeDetect_VerDer_Xilinx_RAMS_BLOCK_1R1W_RBW_rwport_en_7_7_64_80_1_80_64_1_gen
      line_buf1_rsci (
      .clken(line_buf1_rsc_clken),
      .q(line_buf1_rsc_q),
      .re(line_buf1_rsc_re),
      .radr(line_buf1_rsc_radr),
      .we(line_buf1_rsc_we),
      .d(line_buf1_rsc_d),
      .wadr(line_buf1_rsc_wadr),
      .clken_d(1'b1),
      .d_d(line_buf1_rsci_d_d),
      .q_d(line_buf1_rsci_q_d),
      .radr_d(line_buf1_rsci_radr_d),
      .re_d(line_buf1_rsci_re_d_iff),
      .wadr_d(line_buf1_rsci_wadr_d),
      .we_d(line_buf1_rsci_we_d_iff),
      .writeA_w_ram_ir_internal_WMASK_B_d(line_buf1_rsci_we_d_iff),
      .readA_r_ram_ir_internal_RMASK_B_d(line_buf1_rsci_re_d_iff)
    );
  EdgeDetect_IP_EdgeDetect_VerDer_run EdgeDetect_IP_EdgeDetect_VerDer_run_inst (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dat_in_rsc_dat(dat_in_rsc_dat),
      .dat_in_rsc_vld(dat_in_rsc_vld),
      .dat_in_rsc_rdy(dat_in_rsc_rdy),
      .widthIn(widthIn),
      .heightIn(heightIn),
      .pix_chan1_rsc_dat(pix_chan1_rsc_dat),
      .pix_chan1_rsc_vld(pix_chan1_rsc_vld),
      .pix_chan1_rsc_rdy(pix_chan1_rsc_rdy),
      .dy_chan_rsc_dat(dy_chan_rsc_dat),
      .dy_chan_rsc_vld(dy_chan_rsc_vld),
      .dy_chan_rsc_rdy(dy_chan_rsc_rdy),
      .line_buf0_rsci_d_d(line_buf0_rsci_d_d),
      .line_buf0_rsci_q_d(line_buf0_rsci_q_d),
      .line_buf0_rsci_radr_d(line_buf0_rsci_radr_d),
      .line_buf0_rsci_wadr_d(line_buf0_rsci_wadr_d),
      .line_buf1_rsci_d_d(line_buf1_rsci_d_d),
      .line_buf1_rsci_q_d(line_buf1_rsci_q_d),
      .line_buf1_rsci_radr_d(line_buf1_rsci_radr_d),
      .line_buf1_rsci_wadr_d(line_buf1_rsci_wadr_d),
      .line_buf0_rsci_re_d_pff(line_buf0_rsci_re_d_iff),
      .line_buf0_rsci_we_d_pff(line_buf0_rsci_we_d_iff),
      .line_buf1_rsci_re_d_pff(line_buf1_rsci_re_d_iff),
      .line_buf1_rsci_we_d_pff(line_buf1_rsci_we_d_iff)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_HorDer
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_HorDer (
  clk, rst, arst_n, pix_chan1_rsc_dat, pix_chan1_rsc_vld, pix_chan1_rsc_rdy, widthIn,
      heightIn, pix_chan2_rsc_dat, pix_chan2_rsc_vld, pix_chan2_rsc_rdy, dx_chan_rsc_dat,
      dx_chan_rsc_vld, dx_chan_rsc_rdy
);
  input clk;
  input rst;
  input arst_n;
  input [31:0] pix_chan1_rsc_dat;
  input pix_chan1_rsc_vld;
  output pix_chan1_rsc_rdy;
  input [9:0] widthIn;
  input [8:0] heightIn;
  output [31:0] pix_chan2_rsc_dat;
  output pix_chan2_rsc_vld;
  input pix_chan2_rsc_rdy;
  output [35:0] dx_chan_rsc_dat;
  output dx_chan_rsc_vld;
  input dx_chan_rsc_rdy;



  // Interconnect Declarations for Component Instantiations 
  EdgeDetect_IP_EdgeDetect_HorDer_run EdgeDetect_IP_EdgeDetect_HorDer_run_inst (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .pix_chan1_rsc_dat(pix_chan1_rsc_dat),
      .pix_chan1_rsc_vld(pix_chan1_rsc_vld),
      .pix_chan1_rsc_rdy(pix_chan1_rsc_rdy),
      .widthIn(widthIn),
      .heightIn(heightIn),
      .pix_chan2_rsc_dat(pix_chan2_rsc_dat),
      .pix_chan2_rsc_vld(pix_chan2_rsc_vld),
      .pix_chan2_rsc_rdy(pix_chan2_rsc_rdy),
      .dx_chan_rsc_dat(dx_chan_rsc_dat),
      .dx_chan_rsc_vld(dx_chan_rsc_vld),
      .dx_chan_rsc_rdy(dx_chan_rsc_rdy)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_MagAng
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_MagAng (
  clk, rst, arst_n, dx_chan_rsc_dat, dx_chan_rsc_vld, dx_chan_rsc_rdy, dy_chan_rsc_dat,
      dy_chan_rsc_vld, dy_chan_rsc_rdy, pix_chan2_rsc_dat, pix_chan2_rsc_vld, pix_chan2_rsc_rdy,
      widthIn, heightIn, sw_in_rsc_dat, sw_in_triosy_lz, crc32_pix_in_rsc_zout, crc32_pix_in_rsc_lzout,
      crc32_pix_in_rsc_zin, crc32_pix_in_triosy_lz, crc32_dat_out_rsc_zout, crc32_dat_out_rsc_lzout,
      crc32_dat_out_rsc_zin, crc32_dat_out_triosy_lz, dat_out_rsc_dat, dat_out_rsc_vld,
      dat_out_rsc_rdy
);
  input clk;
  input rst;
  input arst_n;
  input [35:0] dx_chan_rsc_dat;
  input dx_chan_rsc_vld;
  output dx_chan_rsc_rdy;
  input [35:0] dy_chan_rsc_dat;
  input dy_chan_rsc_vld;
  output dy_chan_rsc_rdy;
  input [31:0] pix_chan2_rsc_dat;
  input pix_chan2_rsc_vld;
  output pix_chan2_rsc_rdy;
  input [9:0] widthIn;
  input [8:0] heightIn;
  input sw_in_rsc_dat;
  output sw_in_triosy_lz;
  output [31:0] crc32_pix_in_rsc_zout;
  output crc32_pix_in_rsc_lzout;
  input [31:0] crc32_pix_in_rsc_zin;
  output crc32_pix_in_triosy_lz;
  output [31:0] crc32_dat_out_rsc_zout;
  output crc32_dat_out_rsc_lzout;
  input [31:0] crc32_dat_out_rsc_zin;
  output crc32_dat_out_triosy_lz;
  output [33:0] dat_out_rsc_dat;
  output dat_out_rsc_vld;
  input dat_out_rsc_rdy;


  // Interconnect Declarations
  wire sw_in_rsci_idat;


  // Interconnect Declarations for Component Instantiations 
  ccs_in_v1 #(.rscid(32'sd18),
  .width(32'sd1)) sw_in_rsci (
      .dat(sw_in_rsc_dat),
      .idat(sw_in_rsci_idat)
    );
  EdgeDetect_IP_EdgeDetect_MagAng_run EdgeDetect_IP_EdgeDetect_MagAng_run_inst (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dx_chan_rsc_dat(dx_chan_rsc_dat),
      .dx_chan_rsc_vld(dx_chan_rsc_vld),
      .dx_chan_rsc_rdy(dx_chan_rsc_rdy),
      .dy_chan_rsc_dat(dy_chan_rsc_dat),
      .dy_chan_rsc_vld(dy_chan_rsc_vld),
      .dy_chan_rsc_rdy(dy_chan_rsc_rdy),
      .pix_chan2_rsc_dat(pix_chan2_rsc_dat),
      .pix_chan2_rsc_vld(pix_chan2_rsc_vld),
      .pix_chan2_rsc_rdy(pix_chan2_rsc_rdy),
      .widthIn(widthIn),
      .heightIn(heightIn),
      .sw_in_triosy_lz(sw_in_triosy_lz),
      .crc32_pix_in_rsc_zout(crc32_pix_in_rsc_zout),
      .crc32_pix_in_rsc_lzout(crc32_pix_in_rsc_lzout),
      .crc32_pix_in_rsc_zin(crc32_pix_in_rsc_zin),
      .crc32_pix_in_triosy_lz(crc32_pix_in_triosy_lz),
      .crc32_dat_out_rsc_zout(crc32_dat_out_rsc_zout),
      .crc32_dat_out_rsc_lzout(crc32_dat_out_rsc_lzout),
      .crc32_dat_out_rsc_zin(crc32_dat_out_rsc_zin),
      .crc32_dat_out_triosy_lz(crc32_dat_out_triosy_lz),
      .dat_out_rsc_dat(dat_out_rsc_dat),
      .dat_out_rsc_vld(dat_out_rsc_vld),
      .dat_out_rsc_rdy(dat_out_rsc_rdy),
      .sw_in_rsci_idat(sw_in_rsci_idat)
    );
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Top_struct
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Top_struct (
  clk, rst, arst_n, widthIn, heightIn, sw_in_rsc_dat, sw_in_triosy_lz, crc32_pix_in_rsc_zout,
      crc32_pix_in_rsc_lzout, crc32_pix_in_rsc_zin, crc32_pix_in_triosy_lz, crc32_dat_out_rsc_zout,
      crc32_dat_out_rsc_lzout, crc32_dat_out_rsc_zin, crc32_dat_out_triosy_lz, dat_in_rsc_dat_eol,
      dat_in_rsc_dat_sof, dat_in_rsc_dat_pix, dat_in_rsc_vld, dat_in_rsc_rdy, dat_out_rsc_dat_eol,
      dat_out_rsc_dat_sof, dat_out_rsc_dat_pix, dat_out_rsc_vld, dat_out_rsc_rdy,
      line_buf0_rsc_clken, line_buf0_rsc_q, line_buf0_rsc_re, line_buf0_rsc_radr,
      line_buf0_rsc_we, line_buf0_rsc_d, line_buf0_rsc_wadr, line_buf1_rsc_clken,
      line_buf1_rsc_q, line_buf1_rsc_re, line_buf1_rsc_radr, line_buf1_rsc_we, line_buf1_rsc_d,
      line_buf1_rsc_wadr
);
  input clk;
  input rst;
  input arst_n;
  input [9:0] widthIn;
  input [8:0] heightIn;
  input sw_in_rsc_dat;
  output sw_in_triosy_lz;
  output [31:0] crc32_pix_in_rsc_zout;
  output crc32_pix_in_rsc_lzout;
  input [31:0] crc32_pix_in_rsc_zin;
  output crc32_pix_in_triosy_lz;
  output [31:0] crc32_dat_out_rsc_zout;
  output crc32_dat_out_rsc_lzout;
  input [31:0] crc32_dat_out_rsc_zin;
  output crc32_dat_out_triosy_lz;
  input dat_in_rsc_dat_eol;
  input dat_in_rsc_dat_sof;
  input [31:0] dat_in_rsc_dat_pix;
  input dat_in_rsc_vld;
  output dat_in_rsc_rdy;
  output dat_out_rsc_dat_eol;
  output dat_out_rsc_dat_sof;
  output [31:0] dat_out_rsc_dat_pix;
  output dat_out_rsc_vld;
  input dat_out_rsc_rdy;
  output line_buf0_rsc_clken;
  input [63:0] line_buf0_rsc_q;
  output line_buf0_rsc_re;
  output [6:0] line_buf0_rsc_radr;
  output line_buf0_rsc_we;
  output [63:0] line_buf0_rsc_d;
  output [6:0] line_buf0_rsc_wadr;
  output line_buf1_rsc_clken;
  input [63:0] line_buf1_rsc_q;
  output line_buf1_rsc_re;
  output [6:0] line_buf1_rsc_radr;
  output line_buf1_rsc_we;
  output [63:0] line_buf1_rsc_d;
  output [6:0] line_buf1_rsc_wadr;


  // Interconnect Declarations
  wire [31:0] pix_chan1_rsc_dat_n_VerDer_inst;
  wire pix_chan1_rsc_rdy_n_VerDer_inst;
  wire [35:0] dy_chan_rsc_dat_n_VerDer_inst;
  wire dy_chan_rsc_rdy_n_VerDer_inst;
  wire line_buf0_rsc_clken_n_VerDer_inst;
  wire [6:0] line_buf0_rsc_radr_n_VerDer_inst;
  wire [63:0] line_buf0_rsc_d_n_VerDer_inst;
  wire [6:0] line_buf0_rsc_wadr_n_VerDer_inst;
  wire line_buf1_rsc_clken_n_VerDer_inst;
  wire [6:0] line_buf1_rsc_radr_n_VerDer_inst;
  wire [63:0] line_buf1_rsc_d_n_VerDer_inst;
  wire [6:0] line_buf1_rsc_wadr_n_VerDer_inst;
  wire [31:0] pix_chan1_rsc_dat_n_HorDer_inst;
  wire pix_chan1_rsc_vld_n_HorDer_inst;
  wire [31:0] pix_chan2_rsc_dat_n_HorDer_inst;
  wire pix_chan2_rsc_rdy_n_HorDer_inst;
  wire [35:0] dx_chan_rsc_dat_n_HorDer_inst;
  wire [35:0] dy_chan_rsc_dat_n_MagAng_inst;
  wire dy_chan_rsc_vld_n_MagAng_inst;
  wire [31:0] pix_chan2_rsc_dat_n_MagAng_inst;
  wire pix_chan2_rsc_vld_n_MagAng_inst;
  wire [31:0] crc32_pix_in_rsc_zout_n_MagAng_inst;
  wire [31:0] crc32_dat_out_rsc_zout_n_MagAng_inst;
  wire [33:0] dat_out_rsc_dat_n_MagAng_inst;
  wire dat_in_rsc_rdy_n_VerDer_inst_bud;
  wire pix_chan1_rsc_vld_n_VerDer_inst_bud;
  wire pix_chan1_rsc_rdy_n_HorDer_inst_bud;
  wire dy_chan_rsc_vld_n_VerDer_inst_bud;
  wire dy_chan_rsc_rdy_n_MagAng_inst_bud;
  wire line_buf0_rsc_re_n_VerDer_inst_bud;
  wire line_buf0_rsc_we_n_VerDer_inst_bud;
  wire line_buf1_rsc_re_n_VerDer_inst_bud;
  wire line_buf1_rsc_we_n_VerDer_inst_bud;
  wire pix_chan2_rsc_vld_n_HorDer_inst_bud;
  wire pix_chan2_rsc_rdy_n_MagAng_inst_bud;
  wire dx_chan_rsc_vld_n_HorDer_inst_bud;
  wire dx_chan_rsc_rdy_n_MagAng_inst_bud;
  wire sw_in_triosy_lz_n_MagAng_inst_bud;
  wire crc32_pix_in_rsc_lzout_n_MagAng_inst_bud;
  wire crc32_pix_in_triosy_lz_n_MagAng_inst_bud;
  wire crc32_dat_out_rsc_lzout_n_MagAng_inst_bud;
  wire crc32_dat_out_triosy_lz_n_MagAng_inst_bud;
  wire dat_out_rsc_vld_n_MagAng_inst_bud;
  wire pix_chan1_unc_1;
  wire pix_chan1_idle;
  wire dy_chan_unc_1;
  wire dy_chan_idle;
  wire pix_chan2_unc_1;
  wire pix_chan2_idle;


  // Interconnect Declarations for Component Instantiations 
  wire [33:0] nl_VerDer_inst_dat_in_rsc_dat;
  assign nl_VerDer_inst_dat_in_rsc_dat = {dat_in_rsc_dat_eol , dat_in_rsc_dat_sof
      , dat_in_rsc_dat_pix};
  ccs_pipe_v6 #(.rscid(32'sd29),
  .width(32'sd32),
  .sz_width(32'sd1),
  .fifo_sz(32'sd1),
  .log2_sz(32'sd0),
  .ph_clk(32'sd1),
  .ph_en(32'sd0),
  .ph_arst(32'sd0),
  .ph_srst(32'sd1)) pix_chan1_cns_pipe (
      .clk(clk),
      .en(1'b0),
      .arst(arst_n),
      .srst(rst),
      .din_rdy(pix_chan1_rsc_rdy_n_VerDer_inst),
      .din_vld(pix_chan1_rsc_vld_n_VerDer_inst_bud),
      .din(pix_chan1_rsc_dat_n_VerDer_inst),
      .dout_rdy(pix_chan1_rsc_rdy_n_HorDer_inst_bud),
      .dout_vld(pix_chan1_rsc_vld_n_HorDer_inst),
      .dout(pix_chan1_rsc_dat_n_HorDer_inst),
      .sz(pix_chan1_unc_1),
      .sz_req(1'b0),
      .is_idle(pix_chan1_idle)
    );
  ccs_pipe_v6 #(.rscid(32'sd30),
  .width(32'sd36),
  .sz_width(32'sd1),
  .fifo_sz(32'sd3),
  .log2_sz(32'sd2),
  .ph_clk(32'sd1),
  .ph_en(32'sd0),
  .ph_arst(32'sd0),
  .ph_srst(32'sd1)) dy_chan_cns_pipe (
      .clk(clk),
      .en(1'b0),
      .arst(arst_n),
      .srst(rst),
      .din_rdy(dy_chan_rsc_rdy_n_VerDer_inst),
      .din_vld(dy_chan_rsc_vld_n_VerDer_inst_bud),
      .din(dy_chan_rsc_dat_n_VerDer_inst),
      .dout_rdy(dy_chan_rsc_rdy_n_MagAng_inst_bud),
      .dout_vld(dy_chan_rsc_vld_n_MagAng_inst),
      .dout(dy_chan_rsc_dat_n_MagAng_inst),
      .sz(dy_chan_unc_1),
      .sz_req(1'b0),
      .is_idle(dy_chan_idle)
    );
  ccs_pipe_v6 #(.rscid(32'sd31),
  .width(32'sd32),
  .sz_width(32'sd1),
  .fifo_sz(32'sd1),
  .log2_sz(32'sd0),
  .ph_clk(32'sd1),
  .ph_en(32'sd0),
  .ph_arst(32'sd0),
  .ph_srst(32'sd1)) pix_chan2_cns_pipe (
      .clk(clk),
      .en(1'b0),
      .arst(arst_n),
      .srst(rst),
      .din_rdy(pix_chan2_rsc_rdy_n_HorDer_inst),
      .din_vld(pix_chan2_rsc_vld_n_HorDer_inst_bud),
      .din(pix_chan2_rsc_dat_n_HorDer_inst),
      .dout_rdy(pix_chan2_rsc_rdy_n_MagAng_inst_bud),
      .dout_vld(pix_chan2_rsc_vld_n_MagAng_inst),
      .dout(pix_chan2_rsc_dat_n_MagAng_inst),
      .sz(pix_chan2_unc_1),
      .sz_req(1'b0),
      .is_idle(pix_chan2_idle)
    );
  EdgeDetect_IP_EdgeDetect_VerDer VerDer_inst (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dat_in_rsc_dat(nl_VerDer_inst_dat_in_rsc_dat[33:0]),
      .dat_in_rsc_vld(dat_in_rsc_vld),
      .dat_in_rsc_rdy(dat_in_rsc_rdy_n_VerDer_inst_bud),
      .widthIn(widthIn),
      .heightIn(heightIn),
      .pix_chan1_rsc_dat(pix_chan1_rsc_dat_n_VerDer_inst),
      .pix_chan1_rsc_vld(pix_chan1_rsc_vld_n_VerDer_inst_bud),
      .pix_chan1_rsc_rdy(pix_chan1_rsc_rdy_n_VerDer_inst),
      .dy_chan_rsc_dat(dy_chan_rsc_dat_n_VerDer_inst),
      .dy_chan_rsc_vld(dy_chan_rsc_vld_n_VerDer_inst_bud),
      .dy_chan_rsc_rdy(dy_chan_rsc_rdy_n_VerDer_inst),
      .line_buf0_rsc_clken(line_buf0_rsc_clken_n_VerDer_inst),
      .line_buf0_rsc_q(line_buf0_rsc_q),
      .line_buf0_rsc_re(line_buf0_rsc_re_n_VerDer_inst_bud),
      .line_buf0_rsc_radr(line_buf0_rsc_radr_n_VerDer_inst),
      .line_buf0_rsc_we(line_buf0_rsc_we_n_VerDer_inst_bud),
      .line_buf0_rsc_d(line_buf0_rsc_d_n_VerDer_inst),
      .line_buf0_rsc_wadr(line_buf0_rsc_wadr_n_VerDer_inst),
      .line_buf1_rsc_clken(line_buf1_rsc_clken_n_VerDer_inst),
      .line_buf1_rsc_q(line_buf1_rsc_q),
      .line_buf1_rsc_re(line_buf1_rsc_re_n_VerDer_inst_bud),
      .line_buf1_rsc_radr(line_buf1_rsc_radr_n_VerDer_inst),
      .line_buf1_rsc_we(line_buf1_rsc_we_n_VerDer_inst_bud),
      .line_buf1_rsc_d(line_buf1_rsc_d_n_VerDer_inst),
      .line_buf1_rsc_wadr(line_buf1_rsc_wadr_n_VerDer_inst)
    );
  EdgeDetect_IP_EdgeDetect_HorDer HorDer_inst (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .pix_chan1_rsc_dat(pix_chan1_rsc_dat_n_HorDer_inst),
      .pix_chan1_rsc_vld(pix_chan1_rsc_vld_n_HorDer_inst),
      .pix_chan1_rsc_rdy(pix_chan1_rsc_rdy_n_HorDer_inst_bud),
      .widthIn(widthIn),
      .heightIn(heightIn),
      .pix_chan2_rsc_dat(pix_chan2_rsc_dat_n_HorDer_inst),
      .pix_chan2_rsc_vld(pix_chan2_rsc_vld_n_HorDer_inst_bud),
      .pix_chan2_rsc_rdy(pix_chan2_rsc_rdy_n_HorDer_inst),
      .dx_chan_rsc_dat(dx_chan_rsc_dat_n_HorDer_inst),
      .dx_chan_rsc_vld(dx_chan_rsc_vld_n_HorDer_inst_bud),
      .dx_chan_rsc_rdy(dx_chan_rsc_rdy_n_MagAng_inst_bud)
    );
  EdgeDetect_IP_EdgeDetect_MagAng MagAng_inst (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .dx_chan_rsc_dat(dx_chan_rsc_dat_n_HorDer_inst),
      .dx_chan_rsc_vld(dx_chan_rsc_vld_n_HorDer_inst_bud),
      .dx_chan_rsc_rdy(dx_chan_rsc_rdy_n_MagAng_inst_bud),
      .dy_chan_rsc_dat(dy_chan_rsc_dat_n_MagAng_inst),
      .dy_chan_rsc_vld(dy_chan_rsc_vld_n_MagAng_inst),
      .dy_chan_rsc_rdy(dy_chan_rsc_rdy_n_MagAng_inst_bud),
      .pix_chan2_rsc_dat(pix_chan2_rsc_dat_n_MagAng_inst),
      .pix_chan2_rsc_vld(pix_chan2_rsc_vld_n_MagAng_inst),
      .pix_chan2_rsc_rdy(pix_chan2_rsc_rdy_n_MagAng_inst_bud),
      .widthIn(widthIn),
      .heightIn(heightIn),
      .sw_in_rsc_dat(sw_in_rsc_dat),
      .sw_in_triosy_lz(sw_in_triosy_lz_n_MagAng_inst_bud),
      .crc32_pix_in_rsc_zout(crc32_pix_in_rsc_zout_n_MagAng_inst),
      .crc32_pix_in_rsc_lzout(crc32_pix_in_rsc_lzout_n_MagAng_inst_bud),
      .crc32_pix_in_rsc_zin(crc32_pix_in_rsc_zin),
      .crc32_pix_in_triosy_lz(crc32_pix_in_triosy_lz_n_MagAng_inst_bud),
      .crc32_dat_out_rsc_zout(crc32_dat_out_rsc_zout_n_MagAng_inst),
      .crc32_dat_out_rsc_lzout(crc32_dat_out_rsc_lzout_n_MagAng_inst_bud),
      .crc32_dat_out_rsc_zin(crc32_dat_out_rsc_zin),
      .crc32_dat_out_triosy_lz(crc32_dat_out_triosy_lz_n_MagAng_inst_bud),
      .dat_out_rsc_dat(dat_out_rsc_dat_n_MagAng_inst),
      .dat_out_rsc_vld(dat_out_rsc_vld_n_MagAng_inst_bud),
      .dat_out_rsc_rdy(dat_out_rsc_rdy)
    );
  assign dat_out_rsc_dat_pix = dat_out_rsc_dat_n_MagAng_inst[31:0];
  assign dat_out_rsc_dat_sof = dat_out_rsc_dat_n_MagAng_inst[32];
  assign dat_out_rsc_dat_eol = dat_out_rsc_dat_n_MagAng_inst[33];
  assign dat_in_rsc_rdy = dat_in_rsc_rdy_n_VerDer_inst_bud;
  assign line_buf0_rsc_clken = line_buf0_rsc_clken_n_VerDer_inst;
  assign line_buf0_rsc_re = line_buf0_rsc_re_n_VerDer_inst_bud;
  assign line_buf0_rsc_radr = line_buf0_rsc_radr_n_VerDer_inst;
  assign line_buf0_rsc_we = line_buf0_rsc_we_n_VerDer_inst_bud;
  assign line_buf0_rsc_d = line_buf0_rsc_d_n_VerDer_inst;
  assign line_buf0_rsc_wadr = line_buf0_rsc_wadr_n_VerDer_inst;
  assign line_buf1_rsc_clken = line_buf1_rsc_clken_n_VerDer_inst;
  assign line_buf1_rsc_re = line_buf1_rsc_re_n_VerDer_inst_bud;
  assign line_buf1_rsc_radr = line_buf1_rsc_radr_n_VerDer_inst;
  assign line_buf1_rsc_we = line_buf1_rsc_we_n_VerDer_inst_bud;
  assign line_buf1_rsc_d = line_buf1_rsc_d_n_VerDer_inst;
  assign line_buf1_rsc_wadr = line_buf1_rsc_wadr_n_VerDer_inst;
  assign sw_in_triosy_lz = sw_in_triosy_lz_n_MagAng_inst_bud;
  assign crc32_pix_in_rsc_lzout = crc32_pix_in_rsc_lzout_n_MagAng_inst_bud;
  assign crc32_pix_in_rsc_zout = crc32_pix_in_rsc_zout_n_MagAng_inst;
  assign crc32_pix_in_triosy_lz = crc32_pix_in_triosy_lz_n_MagAng_inst_bud;
  assign crc32_dat_out_rsc_lzout = crc32_dat_out_rsc_lzout_n_MagAng_inst_bud;
  assign crc32_dat_out_rsc_zout = crc32_dat_out_rsc_zout_n_MagAng_inst;
  assign crc32_dat_out_triosy_lz = crc32_dat_out_triosy_lz_n_MagAng_inst_bud;
  assign dat_out_rsc_vld = dat_out_rsc_vld_n_MagAng_inst_bud;
endmodule

// ------------------------------------------------------------------
//  Design Unit:    EdgeDetect_IP_EdgeDetect_Top
// ------------------------------------------------------------------


module EdgeDetect_IP_EdgeDetect_Top (
  clk, rst, arst_n, widthIn, heightIn, sw_in_rsc_dat, sw_in_triosy_lz, crc32_pix_in_rsc_zout,
      crc32_pix_in_rsc_lzout, crc32_pix_in_rsc_zin, crc32_pix_in_triosy_lz, crc32_dat_out_rsc_zout,
      crc32_dat_out_rsc_lzout, crc32_dat_out_rsc_zin, crc32_dat_out_triosy_lz, dat_in_rsc_dat,
      dat_in_rsc_vld, dat_in_rsc_rdy, dat_out_rsc_dat, dat_out_rsc_vld, dat_out_rsc_rdy,
      line_buf0_rsc_clken, line_buf0_rsc_q, line_buf0_rsc_re, line_buf0_rsc_radr,
      line_buf0_rsc_we, line_buf0_rsc_d, line_buf0_rsc_wadr, line_buf1_rsc_clken,
      line_buf1_rsc_q, line_buf1_rsc_re, line_buf1_rsc_radr, line_buf1_rsc_we, line_buf1_rsc_d,
      line_buf1_rsc_wadr
);
  input clk;
  input rst;
  input arst_n;
  input [9:0] widthIn;
  input [8:0] heightIn;
  input sw_in_rsc_dat;
  output sw_in_triosy_lz;
  output [31:0] crc32_pix_in_rsc_zout;
  output crc32_pix_in_rsc_lzout;
  input [31:0] crc32_pix_in_rsc_zin;
  output crc32_pix_in_triosy_lz;
  output [31:0] crc32_dat_out_rsc_zout;
  output crc32_dat_out_rsc_lzout;
  input [31:0] crc32_dat_out_rsc_zin;
  output crc32_dat_out_triosy_lz;
  input [33:0] dat_in_rsc_dat;
  input dat_in_rsc_vld;
  output dat_in_rsc_rdy;
  output [33:0] dat_out_rsc_dat;
  output dat_out_rsc_vld;
  input dat_out_rsc_rdy;
  output line_buf0_rsc_clken;
  input [63:0] line_buf0_rsc_q;
  output line_buf0_rsc_re;
  output [6:0] line_buf0_rsc_radr;
  output line_buf0_rsc_we;
  output [63:0] line_buf0_rsc_d;
  output [6:0] line_buf0_rsc_wadr;
  output line_buf1_rsc_clken;
  input [63:0] line_buf1_rsc_q;
  output line_buf1_rsc_re;
  output [6:0] line_buf1_rsc_radr;
  output line_buf1_rsc_we;
  output [63:0] line_buf1_rsc_d;
  output [6:0] line_buf1_rsc_wadr;


  // Interconnect Declarations
  wire dat_out_rsc_dat_eol;
  wire dat_out_rsc_dat_sof;
  wire [31:0] dat_out_rsc_dat_pix;


  // Interconnect Declarations for Component Instantiations 
  wire  nl_EdgeDetect_IP_EdgeDetect_Top_struct_inst_dat_in_rsc_dat_eol;
  assign nl_EdgeDetect_IP_EdgeDetect_Top_struct_inst_dat_in_rsc_dat_eol = dat_in_rsc_dat[33];
  wire  nl_EdgeDetect_IP_EdgeDetect_Top_struct_inst_dat_in_rsc_dat_sof;
  assign nl_EdgeDetect_IP_EdgeDetect_Top_struct_inst_dat_in_rsc_dat_sof = dat_in_rsc_dat[32];
  wire [31:0] nl_EdgeDetect_IP_EdgeDetect_Top_struct_inst_dat_in_rsc_dat_pix;
  assign nl_EdgeDetect_IP_EdgeDetect_Top_struct_inst_dat_in_rsc_dat_pix = dat_in_rsc_dat[31:0];
  EdgeDetect_IP_EdgeDetect_Top_struct EdgeDetect_IP_EdgeDetect_Top_struct_inst (
      .clk(clk),
      .rst(rst),
      .arst_n(arst_n),
      .widthIn(widthIn),
      .heightIn(heightIn),
      .sw_in_rsc_dat(sw_in_rsc_dat),
      .sw_in_triosy_lz(sw_in_triosy_lz),
      .crc32_pix_in_rsc_zout(crc32_pix_in_rsc_zout),
      .crc32_pix_in_rsc_lzout(crc32_pix_in_rsc_lzout),
      .crc32_pix_in_rsc_zin(crc32_pix_in_rsc_zin),
      .crc32_pix_in_triosy_lz(crc32_pix_in_triosy_lz),
      .crc32_dat_out_rsc_zout(crc32_dat_out_rsc_zout),
      .crc32_dat_out_rsc_lzout(crc32_dat_out_rsc_lzout),
      .crc32_dat_out_rsc_zin(crc32_dat_out_rsc_zin),
      .crc32_dat_out_triosy_lz(crc32_dat_out_triosy_lz),
      .dat_in_rsc_dat_eol(nl_EdgeDetect_IP_EdgeDetect_Top_struct_inst_dat_in_rsc_dat_eol),
      .dat_in_rsc_dat_sof(nl_EdgeDetect_IP_EdgeDetect_Top_struct_inst_dat_in_rsc_dat_sof),
      .dat_in_rsc_dat_pix(nl_EdgeDetect_IP_EdgeDetect_Top_struct_inst_dat_in_rsc_dat_pix[31:0]),
      .dat_in_rsc_vld(dat_in_rsc_vld),
      .dat_in_rsc_rdy(dat_in_rsc_rdy),
      .dat_out_rsc_dat_eol(dat_out_rsc_dat_eol),
      .dat_out_rsc_dat_sof(dat_out_rsc_dat_sof),
      .dat_out_rsc_dat_pix(dat_out_rsc_dat_pix),
      .dat_out_rsc_vld(dat_out_rsc_vld),
      .dat_out_rsc_rdy(dat_out_rsc_rdy),
      .line_buf0_rsc_clken(line_buf0_rsc_clken),
      .line_buf0_rsc_q(line_buf0_rsc_q),
      .line_buf0_rsc_re(line_buf0_rsc_re),
      .line_buf0_rsc_radr(line_buf0_rsc_radr),
      .line_buf0_rsc_we(line_buf0_rsc_we),
      .line_buf0_rsc_d(line_buf0_rsc_d),
      .line_buf0_rsc_wadr(line_buf0_rsc_wadr),
      .line_buf1_rsc_clken(line_buf1_rsc_clken),
      .line_buf1_rsc_q(line_buf1_rsc_q),
      .line_buf1_rsc_re(line_buf1_rsc_re),
      .line_buf1_rsc_radr(line_buf1_rsc_radr),
      .line_buf1_rsc_we(line_buf1_rsc_we),
      .line_buf1_rsc_d(line_buf1_rsc_d),
      .line_buf1_rsc_wadr(line_buf1_rsc_wadr)
    );
  assign dat_out_rsc_dat = {dat_out_rsc_dat_eol , dat_out_rsc_dat_sof , dat_out_rsc_dat_pix};
endmodule



