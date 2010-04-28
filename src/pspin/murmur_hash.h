/**
 * @file   murmur_hash.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sat Apr 24 19:13:59 2010
 * 
 * @brief  MurmurHash 2.0 implementation.
 * 
 * Original author: Austin Appleby <aappleby@gmail.com>
 * 
 */

#ifndef _MURMUR_HASH_H_
#define _MURMUR_HASH_H_

#include <limits.h>
#include <stdint.h>

#if __WORDSIZE == 32

/**
 * Type used for ordinary hash lookups
 */
typedef uint32_t state_hash_t;
/**
 * Type used by hashcompact implementation for "big" hash stored
 * in hashtable instead of full states
 */
typedef uint64_t big_state_hash_t;

/*
 * Format codes for printf() 
 */
#define HASH_FMT     "%u"
#define BIG_HASH_FMT "%llu"

/*
 * Maximum possible hash value
 */
#define HASH_MAX UINT32_MAX

/*
 * On 32-bit platform, hashtables use 32-bit hash for lookups
 * and 64-bit for hashcompact method
 */
#define murmur_hash     murmur_hash32
#define murmur_hash_big murmur_hash64_32

/** 
 * @brief Murmur hash, 32-bit.
 * 
 * @param key Data to hash
 * @param len Data size
 * @param seed "Random" seed
 * 
 * @return Hash value
 */
static inline state_hash_t murmur_hash32(const void *key, size_t len, 
										 state_hash_t seed)
{
	/* 'm' and 'r' are mixing constants generated offline.
	 * They're not really 'magic', they just happen to work well.
	 */
	const state_hash_t m = 0x5bd1e995;
	const int r = 24;

	/* Initialize the hash to a 'random' value
	 */
	state_hash_t h = seed ^ len;

	/* Mix 4 bytes at a time into the hash
	 */
	const unsigned char *data = key;

	while (len >= 4) {
		state_hash_t k = *(state_hash_t *)data;

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
 * @brief Murmur hash, 64-bit for 32-bit plarform
 * 
 * @param key Data to hash
 * @param len Data size
 * @param seed "Random" seed
 * 
 * @return Hash value
 */
static inline big_state_hash_t murmur_hash64_32(const void *key, size_t len,
												state_hash_t seed)
{
	const state_hash_t m = 0x5bd1e995;
	const int r = 24;

	state_hash_t h1 = seed ^ len;
	state_hash_t h2 = 0;

	const state_hash_t * data = (const state_hash_t *)key;

	while (len >= 8) {
		state_hash_t k1 = *data++;
		k1 *= m; k1 ^= k1 >> r; k1 *= m;
		h1 *= m; h1 ^= k1;
		len -= 4;

		state_hash_t k2 = *data++;
		k2 *= m; k2 ^= k2 >> r; k2 *= m;
		h2 *= m; h2 ^= k2;
		len -= 4;
	}

	if (len >= 4) {
		state_hash_t k1 = *data++;
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

	big_state_hash_t h = h1;

	h = (h << 32) | h2;

	return h;
}

#elif __WORDSIZE == 64

/**
 * Type used for ordinary hash lookups
 */
typedef uint64_t state_hash_t;
/**
 * Type used by hashcompact implementation for "big" hash stored
 * in hashtable instead of full states
 */
typedef uint64_t big_state_hash_t;

/*
 * Format codes for printf() 
 */
#define HASH_FMT     "%lu"
#define BIG_HASH_FMT "%lu"

/*
 * Maximum possible hash value
 */
#define HASH_MAX UINT64_MAX

/*
 * On 64-bit platform, both hashtable lookups and hashcompact method
 * use 64-bit hashes
 */
#define murmur_hash     murmur_hash64
#define murmur_hash_big murmur_hash64

/** 
 * @brief Murmur hash, 64-bit for 64-bit plarform
 * 
 * @param key Data to hash
 * @param len Data size
 * @param seed "Random" seed
 * 
 * @return Hash value
 */
static inline state_hash_t murmur_hash64(const void *key, size_t len,
										 state_hash_t seed)
{
	const state_hash_t m = 0xc6a4a7935bd1e995;
	const int r = 47;

	state_hash_t h = seed ^ (len * m);

	const state_hash_t * data = (const state_hash_t *)key;
	const state_hash_t * end = data + (len/8);

	while (data != end) {
		state_hash_t k = *data++;

		k *= m;
		k ^= k >> r;
		k *= m;

		h ^= k;
		h *= m;
	}

	const unsigned char * data2 = (const unsigned char*)data;

	switch (len & 7) {
	case 7: h ^= (state_hash_t)data2[6] << 48;
	case 6: h ^= (state_hash_t)data2[5] << 40;
	case 5: h ^= (state_hash_t)data2[4] << 32;
	case 4: h ^= (state_hash_t)data2[3] << 24;
	case 3: h ^= (state_hash_t)data2[2] << 16;
	case 2: h ^= (state_hash_t)data2[1] << 8;
	case 1: h ^= (state_hash_t)data2[0]; h *= m;
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
