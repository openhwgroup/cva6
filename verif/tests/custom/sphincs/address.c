#include <stdint.h>
#include <string.h>

#include "params.h"
#include "utils.h"

/*
 * Specify which level of Merkle tree (the "layer") we're working on
 */
void set_layer_addr(uint32_t addr[8], uint32_t layer)
{
    ((unsigned char *)addr)[SPX_OFFSET_LAYER] = layer;
}

/*
 * Specify which Merkle tree within the level (the "tree address") we're working on
 */
void set_tree_addr(uint32_t addr[8], uint64_t tree)
{
#if (SPX_TREE_HEIGHT * (SPX_D - 1)) > 64
    #error Subtree addressing is currently limited to at most 2^64 trees
#endif
    ull_to_bytes(&((unsigned char *)addr)[SPX_OFFSET_TREE], 8, tree );
}

/*
 * Specify the reason we'll use this address structure for, that is, what
 * hash will we compute with it.  This is used so that unrelated types of
 * hashes don't accidentally get the same address structure.  The type will be
 * one of the SPX_ADDR_TYPE constants
 */
void set_type(uint32_t addr[8], uint32_t type)
{
    ((unsigned char *)addr)[SPX_OFFSET_TYPE] = type;
}

/*
 * Copy the layer and tree fields of the address structure.  This is used
 * when we're doing multiple types of hashes within the same Merkle tree
 */
void copy_subtree_addr(uint32_t out[8], const uint32_t in[8])
{
    memcpy( out, in, SPX_OFFSET_TREE+8 );
}

/* These functions are used for OTS addresses. */

/*
 * Specify which Merkle leaf we're working on; that is, which OTS keypair
 * we're talking about.
 */
void set_keypair_addr(uint32_t addr[8], uint32_t keypair)
{
#if SPX_FULL_HEIGHT/SPX_D > 8
        /* We have > 256 OTS at the bottom of the Merkle tree; to specify */
        /* which one, we'd need to express it in two bytes */
    ((unsigned char *)addr)[SPX_OFFSET_KP_ADDR2] = keypair >> 8;
#endif
    ((unsigned char *)addr)[SPX_OFFSET_KP_ADDR1] = keypair;
}

/*
 * Copy the layer, tree and keypair fields of the address structure.  This is
 * used when we're doing multiple things within the same OTS keypair
 */
void copy_keypair_addr(uint32_t out[8], const uint32_t in[8])
{
    memcpy( out, in, SPX_OFFSET_TREE+8 );
#if SPX_FULL_HEIGHT/SPX_D > 8
    ((unsigned char *)out)[SPX_OFFSET_KP_ADDR2] = ((unsigned char *)in)[SPX_OFFSET_KP_ADDR2];
#endif
    ((unsigned char *)out)[SPX_OFFSET_KP_ADDR1] = ((unsigned char *)in)[SPX_OFFSET_KP_ADDR1];
}

/*
 * Specify which Merkle chain within the OTS we're working with
 * (the chain address)
 */
void set_chain_addr(uint32_t addr[8], uint32_t chain)
{
    ((unsigned char *)addr)[SPX_OFFSET_CHAIN_ADDR] = chain;
}

/*
 * Specify where in the Merkle chain we are
* (the hash address)
 */
void set_hash_addr(uint32_t addr[8], uint32_t hash)
{
    ((unsigned char *)addr)[SPX_OFFSET_HASH_ADDR] = hash;
}

/* These functions are used for all hash tree addresses (including FORS). */

/*
 * Specify the height of the node in the Merkle/FORS tree we are in
 * (the tree height)
 */
void set_tree_height(uint32_t addr[8], uint32_t tree_height)
{
    ((unsigned char *)addr)[SPX_OFFSET_TREE_HGT] = tree_height;
}

/*
 * Specify the distance from the left edge of the node in the Merkle/FORS tree
 * (the tree index)
 */
void set_tree_index(uint32_t addr[8], uint32_t tree_index)
{
    u32_to_bytes(&((unsigned char *)addr)[SPX_OFFSET_TREE_INDEX], tree_index );
}
