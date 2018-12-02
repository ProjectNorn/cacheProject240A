//========================================================//
//  cache.c                                               //
//  Source file for the Cache Simulator                   //
//                                                        //
//  Implement the I-cache, D-Cache and L2-cache as        //
//  described in the README                               //
//========================================================//

#include "cache.h"
#include <memory>
#include <vector>
#include <unordered_map>
#include <cmath>
#include <cassert>

using namespace std;

//
// TODO:Student Information
//
const char *studentName = "Xianze Meng";
const char *studentID   = "A53284319";
const char *email       = "xianze@ucsd.edu";

//------------------------------------//
//        Cache Configuration         //
//------------------------------------//

uint32_t icacheSets;     // Number of sets in the I$
uint32_t icacheAssoc;    // Associativity of the I$
uint32_t icacheHitTime;  // Hit Time of the I$

uint32_t dcacheSets;     // Number of sets in the D$
uint32_t dcacheAssoc;    // Associativity of the D$
uint32_t dcacheHitTime;  // Hit Time of the D$

uint32_t l2cacheSets;    // Number of sets in the L2$
uint32_t l2cacheAssoc;   // Associativity of the L2$
uint32_t l2cacheHitTime; // Hit Time of the L2$
uint32_t inclusive;      // Indicates if the L2 is inclusive

uint32_t blocksize;      // Block/Line size
uint32_t memspeed;       // Latency of Main Memory

//------------------------------------//
//          Cache Statistics          //
//------------------------------------//

uint64_t icacheRefs;       // I$ references
uint64_t icacheMisses;     // I$ misses
uint64_t icachePenalties;  // I$ penalties

uint64_t dcacheRefs;       // D$ references
uint64_t dcacheMisses;     // D$ misses
uint64_t dcachePenalties;  // D$ penalties

uint64_t l2cacheRefs;      // L2$ references
uint64_t l2cacheMisses;    // L2$ misses
uint64_t l2cachePenalties; // L2$ penalties

//------------------------------------//
//        Cache Data Structures       //
//------------------------------------//

//
//TODO: Add your Cache data structures here
//

template<typename T>
class Node {  
public:
  T value;
  shared_ptr<Node> next = nullptr;
  shared_ptr<Node> prev = nullptr;
  Node(T val, shared_ptr<Node> p, shared_ptr<Node> n): value(val), prev(p), next(n){
  }
};

template<typename T>
class speciallist {
  shared_ptr<Node<T>> head_ = nullptr;
  shared_ptr<Node<T>> tail_ = nullptr;
  uint32_t size_ = 0;
public:
  speciallist() {
    head_ = make_shared<Node<T>>(0, nullptr, nullptr);
    tail_ = make_shared<Node<T>>(0, nullptr, nullptr);
    head_->next = tail_;
    tail_->prev = head_;
  }

  shared_ptr<Node<T>> push_front(T val) {
    shared_ptr<Node<T>> node = make_shared<Node<T>>(val, nullptr, nullptr);
    push_front(node);
    return node;
  }

  void push_front(shared_ptr<Node<T>>& node) {
    node->next = head_->next;
    node->prev = head_;
    head_->next->prev = node;    
    head_->next = node;
    size_++;
  }

  shared_ptr<Node<T>> pop_back() {
    if(!size_) {
      return nullptr;
    }
    size_--;
    shared_ptr<Node<T>> n = tail_->prev;
    tail_->prev = tail_->prev->prev;
    tail_->prev->next = tail_;
    return n;
  }

  void remove(shared_ptr<Node<T>> & node) {
    if(node == head_ || node == tail_)
      return;
    node->next->prev = node->prev;
    node->prev->next = node->next;
  }
};

class Cache {
private:
  uint32_t sets_ = 0;
  uint32_t assoc_ = 0;
  uint32_t hittime_ = 0;
  shared_ptr<Cache> next_level_cache_  = nullptr;  
  vector<unordered_map<uint32_t, shared_ptr<Node<uint32_t>>>> hash_tables_; 
  vector<speciallist<uint32_t>> lists_;

  uint32_t block_bits_ = 0;
  uint32_t set_bits_ = 0;
  // uint32_t tag_bits_ = 0;
  uint32_t set_mask_ = 0;
  // uint32_t tag_mask_ = 0;

  uint32_t find_target_set(uint32_t addr) {
    return (addr >> block_bits_) & set_mask_;
  }

  uint32_t find_tag(uint32_t addr) {
    return addr >> block_bits_ >> set_bits_;
  }

public:
  static bool inclusive;
  static uint32_t blocksize;
  static uint32_t memspeed;

  uint64_t& cache_refs;
  uint64_t& cache_misses;
  uint64_t& cache_penalties;

  Cache(uint32_t num_sets, uint32_t num_assoc, uint32_t hittime, uint64_t refs, uint64_t misses, uint64_t penalties) :
  sets_(num_sets), assoc_(num_assoc), hittime_(hittime),  cache_refs(refs), cache_misses(misses), cache_penalties(penalties) {
    hash_tables_.resize(sets_);
    lists_.resize(sets_);

    block_bits_ = (int)log2(blocksize);
    set_bits_ = (int)log2(sets_);
    set_mask_ = (1 << set_bits_) - 1;

    if(num_sets == 0) {
      hittime_ = 0;
    }
  }

  bool is_hit(uint32_t target_set, uint32_t tag) {
    return hash_tables_[target_set].find(tag) == hash_tables_[target_set].end();
  }

  bool add_block(uint32_t addr, uint32_t target_set, uint32_t tag, uint32_t& evict_addr) {
    //no need to evict
    //add block to hash table
    //add block to front of the linked list
    if (hash_tables_[target_set].size() <= this->assoc_) {
      auto block = lists_[target_set].push_front(addr);
      hash_tables_[target_set][tag] = block;      
      return false;
    }
    //needs to evict some other record
    else {
      evict_addr = evict_block(addr);
      return true;
    }
  }

  uint32_t evict_block(uint32_t addr) {
    //extract set and tag
    uint32_t target_set = find_target_set(addr);
    uint32_t tag = find_tag(addr);    
    
    //LRU
    shared_ptr<Node<uint32_t>> block = lists_[target_set].pop_back();
    assert(block != nullptr);
    hash_tables_[target_set].erase(tag);
    return block->value;
  }

  uint32_t access(uint32_t addr, Cache* higher_level_cache) {
    //increment cache refefs
    this->cache_refs++;
    //extract set and tag
    uint32_t target_set = find_target_set(addr);
    uint32_t tag = find_tag(addr);
    
    uint32_t access_time = this->hittime_;
    uint32_t time_penalty = 0;
    //check if this cache is instantiated
    if(this->sets_ == 0) {
      if (next_level_cache_) {
        time_penalty = next_level_cache_->access(addr, nullptr);
      }
      else {
        time_penalty = Cache::memspeed;
      }
    }
    //cache miss
    else if(!is_hit(target_set, tag)) {
      //increment miss counter
      this->cache_misses++;
      
      //there exists a next level cache
      if (next_level_cache_) {
        time_penalty = next_level_cache_->access(addr, this);
      }
      //no next level cache
      else {
        time_penalty = Cache::memspeed;
      }

      //add the block to cache and see if there's evicted block
      uint32_t evict_addr = 0;
      if(add_block(addr, target_set, tag, evict_addr)) {
        //some block evicted. check if this operation needs to be pass up
        if(higher_level_cache && Cache::inclusive) {
          uint32_t a = higher_level_cache->evict_block(evict_addr);
          assert(a == evict_addr);
        }
      }
      
      //update statistics
      this->cache_penalties += time_penalty;

      //access time = hit latency + miss penalty
      access_time += time_penalty;
    }
    else {
      //update LRU
      shared_ptr<Node<uint32_t>> block = hash_tables_[target_set][tag];
      lists_[target_set].remove(block);
      lists_[target_set].push_front(block);
    }

    return access_time;
  }

  void set_next_level_cache(shared_ptr<Cache>& nlc) {
    next_level_cache_ = nlc;
  }

};

class CacheWrapper {
private:  
  shared_ptr<Cache> L1I;
  shared_ptr<Cache> L1D;
  shared_ptr<Cache> L2;
public:
  CacheWrapper()  {
    L1I = make_shared<Cache>(icacheSets, icacheAssoc, icacheHitTime, icacheRefs, icacheMisses, icachePenalties);
    L1D = make_shared<Cache>(dcacheSets, dcacheAssoc, dcacheHitTime, dcacheRefs, dcacheMisses, dcachePenalties);  
    L2  = make_shared<Cache>(l2cacheSets, l2cacheAssoc, l2cacheHitTime, l2cacheRefs, l2cacheMisses, l2cachePenalties);
    L1I->set_next_level_cache(L2);
    L1D->set_next_level_cache(L2);    
  }
  uint32_t icache_access(uint32_t addr) {
    return L1I->access(addr, nullptr);
  }
  uint32_t dcache_access(uint32_t addr) {
    return L1D->access(addr, nullptr);
  }
};

bool Cache::inclusive = (inclusive) ? true : false;
uint32_t Cache::blocksize = blocksize;
uint32_t Cache::memspeed = memspeed;
unique_ptr<CacheWrapper> cache_wrapper;

// END CACHE DATA STRUCTURES

//------------------------------------//
//          Cache Functions           //
//------------------------------------//

// Initialize the Cache Hierarchy
//
void
init_cache()
{
  // Initialize cache stats
  icacheRefs        = 0;
  icacheMisses      = 0;
  icachePenalties   = 0;
  dcacheRefs        = 0;
  dcacheMisses      = 0;
  dcachePenalties   = 0;
  l2cacheRefs       = 0;
  l2cacheMisses     = 0;
  l2cachePenalties  = 0;
  
  //
  //TODO: Initialize Cache Simulator Data Structures
  //

  cache_wrapper = unique_ptr<CacheWrapper>();
}

// Perform a memory access through the icache interface for the address 'addr'
// Return the access time for the memory operation
//
uint32_t
icache_access(uint32_t addr)
{
  //
  //TODO: Implement I$
  //

  return cache_wrapper->icache_access(addr);
}

// Perform a memory access through the dcache interface for the address 'addr'
// Return the access time for the memory operation
//
uint32_t
dcache_access(uint32_t addr)
{
  //
  //TODO: Implement D$
  //
  return cache_wrapper->dcache_access(addr);
}

// Perform a memory access to the l2cache for the address 'addr'
// Return the access time for the memory operation
//
uint32_t
l2cache_access(uint32_t addr)
{
  //
  //TODO: Implement L2$
  //
  return memspeed;
}
