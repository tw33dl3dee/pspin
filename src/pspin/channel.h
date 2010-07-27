/**
 * @file   channel.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sat May  1 23:03:35 2010
 * 
 * @brief  Структуры и операции с каналами.
 *
 */

#ifndef _CHANNEL_H_
#define _CHANNEL_H_

/**
 * Общая структура описателя канала.
 */
struct Channel {
	/**
	 * Текущая длина (кол-во записей в канале)
	 */
	unsigned char len;
	/**
	 * Максимальная длина
	 */
	unsigned char max_len;
};

/**
 * Текущая длина канала
 */
#define CHAN_LEN(chan)							\
	((struct Channel *)(chan))->len

/**
 * Максимальная длина канала
 */
#define CHAN_MAXLEN(chan)						\
	((struct Channel *)(chan))->max_len

/*
 * Макросы для запроса свойств канала
 */
#define CHAN_EMPTY(chan)  (CHAN_LEN(chan) == 0)
#define CHAN_NEMPTY(chan) (CHAN_LEN(chan) > 0)
#define CHAN_FULL(chan)   (CHAN_LEN(chan) == CHAN_MAXLEN(chan))
#define CHAN_NFULL(chan)  (CHAN_LEN(chan) < CHAN_MAXLEN(chan))

/*
 * Операции с каналом:
 * 
 * SEND и RECV увеличивают/уменьшают длину канала.
 * Сравнение с максимальной длиной НЕ проводится.
 */
#define CHAN_SEND(chan) ++CHAN_LEN(chan)
#define CHAN_RECV(chan) --CHAN_LEN(chan)

/** 
 * @brief Доступ к полю некоторой записи канала.
 * 
 * @param chan Канал
 * @param type Тип поля
 * @param entry_size Размер записи канала
 * @param entry_idx Номер требуемой записи
 * @param field_offset Смещение требуемого поля
 */
#define CHAN_FIELD(chan, type, entry_size, entry_idx, field_offset)		\
	(*(type *)&chan[sizeof(struct Channel) + (entry_size)*(entry_idx) + (field_offset)])

#endif /* _CHANNEL_H_ */
