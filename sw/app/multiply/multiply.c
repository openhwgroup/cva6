// See LICENSE for license details.

// *************************************************************************
// multiply function (c version)
// -------------------------------------------------------------------------

int multiply( int x, int y )
{

 int i;
 int result = 0;

 for (i = 0; i < 32; i++) {
   if ((x & 0x1) == 1)
     result = result + y;
       
   x = x >> 1;
   y = y << 1;
 } 
 
 return result;

}

