/**
 * @file   mpi_tags.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Thu Mar 25 07:51:49 2010
 * 
 * @brief  MPI-метки пересылаемых сообщений.
 * 
 */

#ifndef _MPI_TAGS_H_
#define _MPI_TAGS_H_

enum MPI_Tags {
	TagState = 1,				///< сообщение с новым состоянием
	TagMsgCount,				///< сообщение с счетчиком прочих сообщений (для проверки завершения)
	TagTerminate,				///< команда завершения
#ifdef DEBUG
	TagDebugLog,				///< сообщения с отладочным выводом
#endif
};

#endif /* _MPI_TAGS_H_ */
