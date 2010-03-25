/**
 * @file   mpi_tags.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Thu Mar 25 07:51:49 2010
 * 
 * @brief  MPI tags used for communication.
 * 
 */

#ifndef _MPI_TAGS_H_
#define _MPI_TAGS_H_

enum MPI_Tags {
	TagState = 1,				///< message contains new state
	TagMsgCount,				///< message is regular termination checker with current message count
	TagTerminate,				///< message is command to terminate
#ifdef DEBUG
	TagDebugLog,				///< message is debug message
#endif
};

#endif /* _MPI_TAGS_H_ */
