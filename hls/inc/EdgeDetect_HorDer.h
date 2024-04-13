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
  class EdgeDetect_HorDer
  {
  public:
    EdgeDetect_HorDer() {}
  
    #pragma hls_design interface
    void CCS_BLOCK(run)(ac_channel<pixelType4x> &pix_chan1,
                        maxWType                &widthIn,
                        maxHType                &heightIn,
                        ac_channel<pixelType4x> &pix_chan2,
                        ac_channel<gradType4x>  &dx_chan)
    {
      // pixel buffers store pixel history
      pixelType4x pix_buf0;
      pixelType4x pix_buf1;
  
      pixelType4x pix0 = 0;
      pixelType4x pix1 = 0;
      pixelType4x pix2 = 0;
  
      pixelType   pix0_0, pix1_0, pix1_1, pix1_2, pix1_3, pix2_3;
      gradType    dx_0, dx_1, dx_2, dx_3;// 3 2 1 0
      gradType4x  dx;

      HROW: for (maxHType y = 0; ; y++) {
        #pragma hls_pipeline_init_interval 1
        HCOL: for (maxWType x = 0; ; x++) { // HCOL has one extra iteration to ramp-up window
          pix2 = pix_buf1;
          pix1 = pix_buf0;
          if (x <= widthIn/4-1) {
            pix0 = pix_chan1.read(); // Read streaming interface
          }
          if (x == 1) {
            pix2 = pix1; // left boundary (replicate pix1 left to pix2) 
          }
          if (x == widthIn) {
            pix0 = pix1; // right boundary (replicate pix1 right to pix0) 
          }
  
          pix_buf1 = pix_buf0;
          pix_buf0 = pix0;
  
          // Calculate derivative
          pix0_0 = pix0.slc<8>(0);
          pix1_3 = pix1.slc<8>(24);
          pix1_2 = pix1.slc<8>(16);
          pix1_1 = pix1.slc<8>(8);
          pix1_0 = pix1.slc<8>(0);
          pix2_3 = pix2.slc<8>(24);

          dx_3 = pix0_0*kernel[0] + pix1_3*kernel[1] + pix1_2*kernel[2];
          dx_2 = pix1_3*kernel[0] + pix1_2*kernel[1] + pix1_1*kernel[2];
          dx_1 = pix1_2*kernel[0] + pix1_1*kernel[1] + pix1_0*kernel[2];
          dx_0 = pix1_1*kernel[0] + pix1_0*kernel[1] + pix2_3*kernel[2];
          dx.set_slc(0 ,dx_0);
          dx.set_slc(9 ,dx_1);
          dx.set_slc(18,dx_2);
          dx.set_slc(27,dx_3);
          /*
          dx_3 = pix0[7:0]*kernel[0] + pix1[31:24]*kernel[1] + pix0[23:16]*kernel[2];
          dx_2 = pix1[31:24]*kernel[0] + pix1[23:16]*kernel[1] + pix1[15:8]*kernel[2];
          dx_1 = pix1[23:16]*kernel[0] + pix1[15:8]*kernel[1] + pix1[7:0]*kernel[2];
          dx_0 = pix1[15:8]*kernel[0] + pix1[7:0]*kernel[1] + pix2[31:24]*kernel[2];
          */
  
          if (x != 0) { // Write streaming interface
            dx_chan.write(dx); // derivative out {pix3, pix2, pix1, pix0}
            pix_chan2.write(pix1);
          }
          // programmable width exit condition
          if ( x == widthIn/4) {
            break;
          }
        }
        // programmable height exit condition
        if (y == maxHType(heightIn-1)) { // cast to maxHType for RTL code coverage
          break;
        }
      }
    }
  };

}


