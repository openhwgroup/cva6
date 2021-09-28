//===============================================================================
//
//  DOLPHIN DESIGN
//
//-------------------------------------------------------------------------------
//
//      Dolphin Design SAS
//      1bisA Chemin du Pre Carre
//      38240-MEYLAN - FRANCE
//
//-------------------------------------------------------------------------------
//
//      STATEMENT OF USE AND CONFIDENTIALITY
//
//      All rights reserved. This file and the information contained herein is
//      confidential and the property of Dolphin Design. Any unauthorized
//      use, duplication, or disclosure of this information is strictly
//      prohibited and may be unlawful.
//      This file and the information contained herein is for use by DOLPHIN
//      DESIGN's users only. No part of this information may be
//      reproduced, transmitted, transcribed, stored in a retrieval system,
//      or translated into any human or computer language, in any form or by
//      any means without the prior written consent of Dolphin Design.
//      No part of this information may be modified without the consent of
//      Dolphin Design.
//
//===============================================================================



initial begin
   #1;
   $display("** Note: i2c, force I2C mem to be fast");
   force i_vip_complex.gen_alternate_0.i_i2c0_mem_0.tWC=100000;
   force i_vip_complex.gen_alternate_0.i_i2c1_mem_0.tWC=100000;
   force i_vip_complex.gen_alternate_0.i_i2c2_mem_0.tWC=100000;
   test_over=1'b1;
end
