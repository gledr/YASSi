/* Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
 *
 * This file is part of CREST, which is distributed under the revised
 * BSD license.  A copy of this license can be found in the file LICENSE.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
 * for details.
 */

//#include <crest.h>
#include <stdio.h>
#define SIZE_A 10
#define SIZE_B_1 10
#define SIZE_B_2 10
int A[SIZE_A];
char B[SIZE_B_1][SIZE_B_2];

int main(void) {
  int x,y, i, j;
  
  //CREST_int(x);
  //CREST_int(y);
  
  // if ((x < 0) || (x >= 97))
  //  return 0;
  //if ((y < 0) || (y >= 45))
  //return 0;
   
   for (i = 0; i < SIZE_A; i++) {
   A[i] = i;
   //printf("A[%d] = %d\n", i, i);
   }
  
  for (i = 0; i < SIZE_B_1; i++) {
	for (j = 0; j < SIZE_B_2; j++) {
	  B[i][j] = i + j;
	  // printf("B[%d][%d] = %d\n", i,j, i+j);
	}
  }
  
  if (A[x] == 0) {
    /*
     * CREST cannot solve for 'x' to reach this branch because it does
     * not treat array indexing symbolically.
     */
	printf("Hello!\n");
    	return 1;
  }
  
  if (B[x][y] == 0) {
    /*
     * CREST cannot solve for 'x' and 'y' to reach this branch because
     * it does not treat array indexing symbolically.
     */
		printf("World!\n");
  		return 3;
  	}
  
  return 0;
}
