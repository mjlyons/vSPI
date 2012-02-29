/*
 * Empty C++ Application
 */

#include <stdio.h>
#include "xil_types.h"

u32 * pSpiifcBase = (u32 *)0x85000000;
u32 * pMosiBase = (u32 *)0x85010000;
u32 * pMisoBase = (u32 *)0x85011000;

int main()
{
	xil_printf("Reg0 @ 0x%08X\n", pSpiifcBase);
	xil_printf("Saving word to Reg0... ");
	*pSpiifcBase = 0x87654321;
	xil_printf("done... verifying... ");
	if (0x87654321 == *pSpiifcBase) {
		xil_printf("PASS.\n");
	} else {
		xil_printf("FAIL. (actual=0x%08X)\n", *pSpiifcBase);
	}
	xil_printf("\n");

	xil_printf("MOSI @ 0x%08X\n", pMosiBase);
	xil_printf("Saving word to Mem0 (MOSI)...");
    *pMosiBase = 0x12345678;
    xil_printf("done... verifying... ");
    if (0x12345678 == *pMosiBase) {
    	xil_printf("PASS.\n");
    } else {
    	xil_printf("FAIL. (actual=0x%08X)\n", *pMosiBase);
    }
    xil_printf("\n");

    xil_printf("MISO @ 0x%08X\n", pMisoBase);
    xil_printf("Saving word to Mem1 (MISO)... ");
    *pMisoBase = 0xFEEDFACE;
    xil_printf("done... verifying... ");
    if (0xFEEDFACE == *pMisoBase) {
    	xil_printf("PASS.\n");
    } else {
    	xil_printf("FAIL. (actual=0x%08X)\n", *pMosiBase);
    }
    xil_printf("\n");

	return 0;
}
