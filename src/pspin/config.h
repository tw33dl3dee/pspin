/**
 * @file   config.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Mon Apr 19 20:12:43 2010
 * 
 * @brief  Конфигурая времени компиляции
 * 
 */

#ifndef _PSPIN_CONFIG_H
#define _PSPIN_CONFIG_H

/*
 * Константы размера
 */
#define kiB 1024L
#define MiB (kiB*kiB)
#define GiB (MiB*kiB)

/*
 * Параметры эмуляции
 */
#ifdef EMULATION
/**
 * Число имитируемых узлов
 */
#	define NODECOUNT 4
#endif

/*
 * Параметры MPI
 */
#ifdef MPI
#endif

/**
 * Проверять IP конечных (тупиковых) состояний
 */
#define ENDSTATE

/*
 * Выбор функции распределения между узлами
 */

/**
 * Использовать целиковый хэш состояния
 */
#undef STATE_PARTITION_HASH
/**
 * Использовать хэш локального состояния первых N процессов
 */
#define STATE_PARTITION_PROC
/**
 * Использовать хэш локального состояния первых N процессов без их IP
 */
#undef STATE_PARTITION_PROC_NOIP

/**
 * При распределении по первым N процессам, содержит N
 */
#define PARTITION_PROC_COUNT 1

/* 
 * Выбор алгоритма хэширования
 */
/**
 * Битовое хэширование
 */
#undef BITSTATE
/**
 * Двухуровневое хэширование (hashcompact)
 */
#undef HASHCOMPACT
/**
 * Полное хэширование с открытой адресацией
 */
#define FULLSTATE

/*
 * Параметры хэш-таблицы а алгоритма хэширования
 */

/**
 * Размер хэш-таблицы (в байтах)
 */
#define HASHTABLE_SIZE (512*MiB)

/**
 * При считывании состояний из сетевой очереди, немедленно копировать из в локальную
 * ПЕРЕД обработкой (уменьшает сетевые задержки, увеличивает расход памяти).
 * 
 * Не рекомендуется для битового хэширования, поскольку может сильно увеличить
 * требуемый объем памяти для очереди поиска.
 * 
 * При полном хранении состояний эта опция является обязательной (игнорируется),
 * в противном случае указатели в хэш-таблице становятся неверными.
 */
#define NETWORK_TO_LOCAL_QUEUE

#ifdef FULLSTATE
/**
 * Размер памяти, выделяемой под пространство состояний (посещенных и в очереди)
 */
#	define STATESPACE_SIZE (512*MiB)
/*
 * При полном хэшировании состояния всегда копируются из сетевой очереди в локальную
 */
#undef  NETWORK_TO_LOCAL_QUEUE
#define NETWORK_TO_LOCAL_QUEUE
#else
/**
 * Размер памяти, выделяемой под очередь поиска (в байтах)
 *
 * При битовом или вторичном хэшировании, состояния в очереди поиска хранятся отдельно.
 * При полном хэшировании параметр не используется, поскольку состояния в очереди хранятся 
 * вместе с посещенными (используется STATESPACE_SIZE).
 */
#	define BFS_QUEUE_SIZE  128*MiB
#endif

#ifdef BITSTATE 
/**
 * Количество хэш-функций для битового хэширования
 */
#	define BITSTATE_HASH_COUNT 3
#endif

#ifdef HASHCOMPACT
/**
 * Размер вторичного хэша (hashcompact)
 */
#	define HASHCOMPACT_BITS 64
#endif

#endif /* _PSPIN_CONFIG_H */
