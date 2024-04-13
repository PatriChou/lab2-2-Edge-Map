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


namespace EdgeDetect_IP {

  class EdgeDetect_VerDer
  {
  private:
  
  public:
    EdgeDetect_VerDer() {}
  
    #pragma hls_design interface
    void CCS_BLOCK(run)(ac_channel<Stream_t>      &dat_in,
                        maxWType                  &widthIn,
                        maxHType                  &heightIn,
                        ac_channel<pixelType4x>   &pix_chan1,
                        ac_channel<gradType4x>    &dy_chan)
    {
      // Line buffers store pixel line history - Mapped to RAM
      pixelType8x line_buf0[maxImageWidth/8]; 
      pixelType8x line_buf1[maxImageWidth/8]; 
      pixelType8x rdbuf0_pix, rdbuf1_pix;
      pixelType8x wrbuf0_pix, wrbuf1_pix;
      Stream_t    pix0, pix1, pix2;
      pixelType   pix0_0, pix0_1, pix0_2, pix0_3, pix1_0, pix1_1, pix1_2, pix1_3, pix2_0, pix2_1, pix2_2, pix2_3; //3 2 1 0
      gradType    dy_0, dy_1, dy_2, dy_3;
      gradType4x  dy;
  
      // Remove loop upperbounds for RTL code coverage
      // Use bit accurate data types on loop iterator
      VROW: for (maxHType y = 0; ; y++) { // VROW has one extra iteration to ramp-up window
        #pragma hls_pipeline_init_interval 1
        VCOL: for (maxWType x = 0; ; x++) {
          if (y <= heightIn-1) {
            pix0 = dat_in.read(); // Read streaming interface
          }
          // Write data cache, write lower 8 on even iterations of COL loop, upper 8 on odd
          if ( (x&1) == 0 ) {
            wrbuf0_pix.set_slc(0,pix0.pix);
          } else {
            wrbuf0_pix.set_slc(32,pix0.pix);
          }
          // Read line buffers into read buffer caches on even iterations of COL loop
          if ( (x&1) == 0 ) {
            // vertical window of pixels
            rdbuf1_pix = line_buf1[x/2];
            rdbuf0_pix = line_buf0[x/2];
          } else { // Write line buffer caches on odd iterations of COL loop
            line_buf1[x/2] = rdbuf0_pix; // copy previous line
            line_buf0[x/2] = wrbuf0_pix; // store current line
          }
          // Get 8-bit data from read buffer caches, lower 8 on even iterations of COL loop
          pix2.pix = ((x&1)==0) ? rdbuf1_pix.slc<32>(0) : rdbuf1_pix.slc<32>(32);
          pix1.pix = ((x&1)==0) ? rdbuf0_pix.slc<32>(0) : rdbuf0_pix.slc<32>(32);
  
          // Boundary condition processing
          if (y == 1) {
            pix2 = pix1; // top boundary (replicate pix1 up to pix2)
          }
          if (y == heightIn) {
            pix0 = pix1; // bottom boundary (replicate pix1 down to pix0)
          }
          pix0_0 = pix0.pix.slc<8>(0);
          pix0_1 = pix0.pix.slc<8>(8);
          pix0_2 = pix0.pix.slc<8>(16);
          pix0_3 = pix0.pix.slc<8>(24);
          pix1_0 = pix1.pix.slc<8>(0);
          pix1_1 = pix1.pix.slc<8>(8);
          pix1_2 = pix1.pix.slc<8>(16);
          pix1_3 = pix1.pix.slc<8>(24);
          pix2_0 = pix2.pix.slc<8>(0);
          pix2_1 = pix2.pix.slc<8>(8);
          pix2_2 = pix2.pix.slc<8>(16);
          pix2_3 = pix2.pix.slc<8>(24);
          // Calculate derivative
          dy_0 = pix2_0*kernel[0] + pix1_0*kernel[1] + pix0_0*kernel[2];
          dy_1 = pix2_1*kernel[0] + pix1_1*kernel[1] + pix0_1*kernel[2];
          dy_2 = pix2_2*kernel[0] + pix1_2*kernel[1] + pix0_2*kernel[2];
          dy_3 = pix2_3*kernel[0] + pix1_3*kernel[1] + pix0_3*kernel[2];
          dy.set_slc(0 ,dy_0);
          dy.set_slc(9 ,dy_1);
          dy.set_slc(18,dy_2);
          dy.set_slc(27,dy_3);
          if (y != 0) { // Write streaming interfaces
            pix_chan1.write(pix1.pix); // Pass thru original data {pix3_1,pix2_1,pix1_1,pix0_1}
            dy_chan.write(dy); // derivative output {pix3,pix2,pix1,pix0}
          }
          // programmable width exit condition
          if (x == maxWType(widthIn/4-1)) { // cast to maxWType for RTL code coverage
            break;
          }
        }
        // programmable height exit condition
        if (y == heightIn) {
          break;
        }
      }
    }
  };

}


