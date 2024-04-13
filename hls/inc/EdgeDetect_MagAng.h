/**************************************************************************
 *                                                                        *
 *  Edge Detect Design Walkthrough for HLS                                *
 *                                                                        *
 *  Software Version: 1.0                                                 *
 *                                                                        *
 *  Release Date    : Tue Jan 14 15:40:43 PST 2020                        *
 *  Release Type    : Production Release                                  *
 *  Release Build   : 1.0.0                                               *
 *                                                                        *
 *  Copyright 2020, Siemens                                               *
 *                                                                        *
 **************************************************************************
 *  Licensed under the Apache License, Version 2.0 (the "License");       *
 *  you may not use this file except in compliance with the License.      *
 *  You may obtain a copy of the License at                               *
 *                                                                        *
 *      http://www.apache.org/licenses/LICENSE-2.0                        *
 *                                                                        *
 *  Unless required by applicable law or agreed to in writing, software   *
 *  distributed under the License is distributed on an "AS IS" BASIS,     *
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or       *
 *  implied.                                                              *
 *  See the License for the specific language governing permissions and   *
 *  limitations under the License.                                        *
 **************************************************************************
 *                                                                        *
 *  The most recent version of this package is available at github.       *
 *                                                                        *
 *************************************************************************/
#pragma once

#include "EdgeDetect_defs.h"
#include <mc_scverify.h>


namespace EdgeDetect_IP 
{
  class EdgeDetect_MagAng
  {
  public:
    EdgeDetect_MagAng() {}
  
    #pragma hls_design interface
    void CCS_BLOCK(run)(ac_channel<gradType4x>  &dx_chan,
                        ac_channel<gradType4x>  &dy_chan,
                        ac_channel<pixelType4x> &pix_chan2,
                        maxWType              &widthIn,
                        maxHType              &heightIn,
                        bool                  &sw_in,
                        uint32                &crc32_pix_in,
                        uint32                &crc32_dat_out,
                        ac_channel<Stream_t>  &dat_out)
    { 
      gradType dx3, dy3, dx2, dy2, dx1, dy1, dx0, dy0;
      uint8    dx3_abs, dy3_abs, dx2_abs, dy2_abs, dx1_abs, dy1_abs, dx0_abs, dy0_abs;
      sumType  abs_sum_0, abs_sum_1, abs_sum_2, abs_sum_3; // fixed point integer for sqrt
      uint8    sum_0, sum_1, sum_2, sum_3;
      uint8    over_flow = 255;
      gradType4x   dx, dy;
      pixelType4x  pix2;
      Stream_t     sum;

      crc32_pix_in = 0XFFFFFFFF;
      crc32_dat_out = 0XFFFFFFFF;
      MROW: for (maxHType y = 0; ; y++) {
        #pragma hls_pipeline_init_interval 1
        MCOL: for (maxWType x = 0; ; x++) {
          dx = dx_chan.read();
          dy = dy_chan.read();
          dx0 = dx.slc<9>(0);
          dy0 = dy.slc<9>(0);
          dx1 = dx.slc<9>(9);
          dy1 = dy.slc<9>(9);
          dx2 = dx.slc<9>(18);
          dy2 = dy.slc<9>(18);
          dx3 = dx.slc<9>(27);
          dy3 = dy.slc<9>(27);
          
          dx0_abs = (dx0[8]) ? (-dx0).slc<8>(0) : dx0.slc<8>(0);
          dy0_abs = (dy0[8]) ? (-dy0).slc<8>(0) : dy0.slc<8>(0);
          dx1_abs = (dx1[8]) ? (-dx1).slc<8>(0) : dx1.slc<8>(0);
          dy1_abs = (dy1[8]) ? (-dy1).slc<8>(0) : dy1.slc<8>(0);
          dx2_abs = (dx2[8]) ? (-dx2).slc<8>(0) : dx2.slc<8>(0);
          dy2_abs = (dy2[8]) ? (-dy2).slc<8>(0) : dy2.slc<8>(0);
          dx3_abs = (dx3[8]) ? (-dx3).slc<8>(0) : dx3.slc<8>(0);
          dy3_abs = (dy3[8]) ? (-dy3).slc<8>(0) : dy3.slc<8>(0);
          
          abs_sum_0 = (dx0_abs + dy0_abs);
          abs_sum_1 = (dx1_abs + dy1_abs);
          abs_sum_2 = (dx2_abs + dy2_abs);
          abs_sum_3 = (dx3_abs + dy3_abs);
          
          sum_0 = (abs_sum_0[8]) ? over_flow : abs_sum_0.slc<8>(0);
          sum_1 = (abs_sum_1[8]) ? over_flow : abs_sum_1.slc<8>(0);
          sum_2 = (abs_sum_2[8]) ? over_flow : abs_sum_2.slc<8>(0);
          sum_3 = (abs_sum_3[8]) ? over_flow : abs_sum_3.slc<8>(0);
          
          
          sum.pix.set_slc(0 ,sum_0);
          sum.pix.set_slc(8 ,sum_1);
          sum.pix.set_slc(16,sum_2);
          sum.pix.set_slc(24,sum_3);
          sum.sof=(x==0&&y==0);
          sum.eol=(x==maxWType(widthIn-4));

          pix2=pix_chan2.read();
          crc32_pix_in = calc_crc32(crc32_pix_in, pix2);
          if (sw_in == 1) {
            sum.pix.set_slc(0 ,sum_0);
            sum.pix.set_slc(8 ,sum_1);
            sum.pix.set_slc(16,sum_2);
            sum.pix.set_slc(24,sum_3);
            crc32_dat_out = calc_crc32(crc32_dat_out, sum.pix);
          } else {
            sum.pix.set_slc(0,pix2);
            crc32_dat_out = calc_crc32(crc32_dat_out, sum.pix);
          }
          dat_out.write(sum);
          // programmable width exit condition
          if (x == maxWType(widthIn/4-1)) { // cast to maxWType for RTL code coverage
            break;
          }
        }
        // programmable height exit condition
        if (y == maxHType(heightIn-1)) { // cast to maxHType for RTL code coverage
          break;
        }
      }
          crc32_pix_in=~crc32_pix_in;
          crc32_dat_out=~crc32_dat_out;
    }
    private:
    template <int len>
    uint32 calc_crc32(uint32 crc_in, ac_int<len, false> dat_in)
    {
      const uint32 CRC_POLY = 0xEDB88320;
      uint32 crc_tmp = crc_in;

      #pragma hls_unroll yes
      for(int i=0; i<len; i++)
      {
        uint1 tmp_bit = crc_tmp[0] ^ dat_in[i];

        uint31 mask;

        #pragma hls_unroll yes
        for(int i=0; i<31; i++)
          mask[i] = tmp_bit & CRC_POLY[i];

        uint31 crc_tmp_h31 = crc_tmp.slc<31>(1);
   
        crc_tmp_h31 ^= mask;
        
        crc_tmp.set_slc(31,tmp_bit);
        crc_tmp.set_slc(0,crc_tmp_h31);
      }
      return crc_tmp;
    }
  };
}


