/**
 * @file   murmur_hash.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sat Apr 24 19:13:59 2010
 * 
 * @brief  Хэш-функция MurmurHash 2.0.
 * 
 * Реализация: Austin Appleby <aappleby@gmail.com>
 * 
 */

#ifndef _MURMUR_HASH_H_
#define _MURMUR_HASH_H_

#include <limits.h>
#include <stdint.h>

#if __WORDSIZE == 32

/**
 * Тип, используемый для инициализатора хэш-функции
 */
typedef uint32_t hash_seed_t;
/**
 * Тип, используемый для хэшей состояний.
 */
typedef uint64_t state_hash_t;
/**
 * Тип, используемый для вторичного хэша (hashcompact)
 */
typedef uint64_t big_state_hash_t;

/*
 * Коды форматирования для printf()
 */
#define HASH_FMT     "%llu"
#define BIG_HASH_FMT "%llu"

/*
 * Максимальное значения хэша
 */
#define HASH_MAX UINT64_MAX

/*
 * На 32-битных платформах используется 64-битный хэш (необходимо для битового хэширования)
 */
#define murmur_hash     murmur_hash64_32
#define murmur_hash_big murmur_hash64_32

/** 
 * @brief Murmur hash, 32-битный.
 * 
 * @param key Указатель на данные
 * @param len Размер данных 
 * @param seed Начальое значение (произвольлное)
 * 
 * @return Значениие хэш-функции
 */
static inline uint32_t murmur_hash32(const void *key, size_t len, uint32_t seed)
{
	/* 'm' and 'r' are mixing constants generated offline.
	 * They're not really 'magic', they just happen to work well.
	 */
	const uint32_t m = 0x5bd1e995;
	const int r = 24;

	/* Initialize the hash to a 'random' value
	 */
	uint32_t h = seed ^ len;

	/* Mix 4 bytes at a time into the hash
	 */
	const unsigned char *data = key;

	while (len >= 4) {
		uint32_t k = *(uint32_t *)data;

		k *= m;
		k ^= k >> r;
		k *= m;

		h *= m;
		h ^= k;

		data += 4;
		len -= 4;
	}

	/* Handle the last few bytes of the input array
	 */
	switch (len) {
	case 3: h ^= data[2] << 16;
	case 2: h ^= data[1] << 8;
	case 1: h ^= data[0]; h *= m;
	}

	/* Do a few final mixes of the hash to ensure the last few
	 * bytes are well-incorporated.
	 */
	h ^= h >> 13;
	h *= m;
	h ^= h >> 15;

	return h;
}

/** 
 * @brief Murmur hash, 64-битный для 32-битных платформ.
 * 
 * @param key Указатель на данные
 * @param len Размер данных 
 * @param seed Начальое значение (произвольлное)
 * 
 * @return Значениие хэш-функции
 */
static inline uint64_t murmur_hash64_32(const void *key, size_t len, uint32_t seed)
{
	const uint32_t m = 0x5bd1e995;
	const int r = 24;

	uint32_t h1 = seed ^ len;
	uint32_t h2 = 0;

	const uint32_t * data = (const uint32_t *)key;

	while (len >= 8) {
		uint32_t k1 = *data++;
		k1 *= m; k1 ^= k1 >> r; k1 *= m;
		h1 *= m; h1 ^= k1;
		len -= 4;

		uint32_t k2 = *data++;
		k2 *= m; k2 ^= k2 >> r; k2 *= m;
		h2 *= m; h2 ^= k2;
		len -= 4;
	}

	if (len >= 4) {
		uint32_t k1 = *data++;
		k1 *= m; k1 ^= k1 >> r; k1 *= m;
		h1 *= m; h1 ^= k1;
		len -= 4;
	}

	switch (len) {
	case 3: h2 ^= ((unsigned char*)data)[2] << 16;
	case 2: h2 ^= ((unsigned char*)data)[1] << 8;
	case 1: h2 ^= ((unsigned char*)data)[0]; h2 *= m;
	}

	h1 ^= h2 >> 18; h1 *= m;
	h2 ^= h1 >> 22; h2 *= m;
	h1 ^= h2 >> 17; h1 *= m;
	h2 ^= h1 >> 19; h2 *= m;

	uint64_t h = h1;

	h = (h << 32) | h2;

	return h;
}

#elif __WORDSIZE == 64

/**
 * Тип, используемый для инициализатора хэш-функции
 */
typedef uint64_t hash_seed_t;
/**
 * Тип, используемый для хэшей состояний.
 */
typedef uint64_t state_hash_t;
/**
 * Тип, используемый для вторичного хэша (hashcompact)
 */
typedef uint64_t big_state_hash_t;

/*
 * Коды форматирования для printf()
 */
#define HASH_FMT     "%lu"
#define BIG_HASH_FMT "%lu"

/*
 * Максимальное значения хэша
 */
#define HASH_MAX UINT64_MAX

/*
 * На 64-битных платформах используется 64-битный хэш
 */
#define murmur_hash     murmur_hash64
#define murmur_hash_big murmur_hash64

/** 
 * @brief Murmur hash, 64-битный для 64-битных платформ.
 * 
 * @param key Указатель на данные
 * @param len Размер данных 
 * @param seed Начальое значение (произвольлное)
 * 
 * @return Значениие хэш-функции
 */
static inline uint64_t murmur_hash64(const void *key, size_t len, uint64_t seed)
{
	const uint64_t m = 0xc6a4a7935bd1e995;
	const int r = 47;

	uint64_t h = seed ^ (len * m);

	const uint64_t * data = (const uint64_t *)key;
	const uint64_t * end = data + (len/8);

	while (data != end) {
		uint64_t k = *data++;

		k *= m;
		k ^= k >> r;
		k *= m;

		h ^= k;
		h *= m;
	}

	const unsigned char * data2 = (const unsigned char*)data;

	switch (len & 7) {
	case 7: h ^= (uint64_t)data2[6] << 48;
	case 6: h ^= (uint64_t)data2[5] << 40;
	case 5: h ^= (uint64_t)data2[4] << 32;
	case 4: h ^= (uint64_t)data2[3] << 24;
	case 3: h ^= (uint64_t)data2[2] << 16;
	case 2: h ^= (uint64_t)data2[1] << 8;
	case 1: h ^= (uint64_t)data2[0]; h *= m;
	}

	h ^= h >> r;
	h *= m;
	h ^= h >> r;

	return h;
}

#else /* __WORDSIZE */

#error "Only 32- and 64-bit platforms are supported"

#endif

#endif /* _MURMUR_HASH_H_ */
