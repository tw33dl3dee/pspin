/**
 * @file   state.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Mon Dec 28 19:52:41 2009
 * 
 * @brief  
 * 
 * 
 */

#ifndef _STATE_H_
#define _STATE_H_

struct Process {
    unsigned char _ip ;
    unsigned char _proctype ;
	char data[0];
};

#define STATE_DECL
#include CODEGEN_FILE
#undef  STATE_DECL

#define PROC_DECL
#include CODEGEN_FILE
#undef  PROC_DECL

#endif /* _STATE_H_ */
