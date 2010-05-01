/**
 * @file   channel.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sat May  1 23:03:35 2010
 * 
 * @brief  Channel operations and structures.
 *
 */

#ifndef _CHANNEL_H_
#define _CHANNEL_H_

/**
 * General channel structure
 */
struct Channel {
	/**
	 * Current length
	 */
	unsigned char len;
	/**
	 * Max length
	 */
	unsigned char max_len;
};

/**
 * Retrieves current channel length
 */
#define CHAN_LEN(chan)						\
	((struct Channel *)(chan))->len

/**
 * Retrieves max channel length
 */
#define CHAN_MAXLEN(chan)						\
	((struct Channel *)(chan))->max_len

/*
 * Channel querying macros
 */
#define CHAN_EMPTY(chan)  (CHAN_LEN(chan) == 0)
#define CHAN_NEMPTY(chan) (CHAN_LEN(chan) > 0)
#define CHAN_FULL(chan)   (CHAN_LEN(chan) == CHAN_MAXLEN(chan))
#define CHAN_NFULL(chan)  (CHAN_LEN(chan) < CHAN_MAXLEN(chan))

/**
 * Size occupied by channel length/max length
 */
#define CHAN_LEN_SIZE (sizeof(CHAN_LEN(NULL)))

/**
 * Typename that stores channel length/max length
 */
#define CHAN_LEN_TYPE __typeof__(CHAN_LEN(NULL))

/*
 * Channel operations:
 * 
 * SEND and RECV increase/decrease current length.
 * The do NOT check current length against max.
 */
#define CHAN_SEND(chan) ++CHAN_LEN(chan)
#define CHAN_RECV(chan) --CHAN_LEN(chan)

/** 
 * @brief Access field of a channel entry.
 * 
 * @param chan Channel
 * @param type Field type
 * @param entry_size Size of channel entry
 * @param entry_idx Index of entry referenced
 * @param field_offset Offset of field referenced
 */
#define CHAN_FIELD(chan, type, entry_size, entry_idx, field_offset)		\
	*(type *)&chan[sizeof(struct Channel) + (entry_size)*(entry_idx) + (field_offset)]

#endif /* _CHANNEL_H_ */
