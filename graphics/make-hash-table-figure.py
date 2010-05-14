#! /usr/bin/python -t
# encoding: utf8 
# Last edited on 2009-04-12 18:29:53 by stolfilocal

PROG_NAME = "make-hash-table-figure"
PROG_DESC = "Generates an SVG illustration for the Wikipedia hash table article"
PROG_VERS = "1.0"

import sys
import re
import os
sys.path[1:0] = [ sys.path[0] + '/../lib', os.path.expandvars('${STOLFIHOME}/lib'), '.' ] 

from decimal import *
from datetime import date

class Options :
  back = None;
  nkeys = None;
  funcbox = None;
  sparse = None;
  keys = None;
  values = None;
  collisions = None;
  links = None;
  overflow = None;
  err = None;

def parse_args():
  op = Options();
  op.err = None
  op.back = None
  op.nkeys = 5
  op.funcbox = 0
  op.sparse = 1
  op.keys = 1
  op.values = 0
  op.collisions = 1
  op.links = 1
  op.overflow = "SP"
  return op
  ################################################################

def dts(x) :
  "Converts the decimal number {x} to string."
  return ("%r" % x)
  ################################################################

class HashTable :
  "Describes the contents of a hash table.\n" \
  "\n" \
  "  Fields are:\n"
  "    {tb.nkeys} = number of VISIBLE key boxes in \"keys\" column.\n" \
  "    {tb.nbucs} = number of VISIBLE hash/bucket boxes in bucket array, including \":\" entries.\n" \
  "    {tb.novfs} = number of VISIBLE entry boxes in \"overflow\" column.\n" \
  "\n" \
  "    {tb.key_str[0..nkeys-1]} = the strings to show in each visible key box.\n" \
  "    {tb.val_str[0..nkeys-1]} = the corresponding values.\n" \
  "    {tb.key_sty[0..nkeys-1]} = the style of each key box (\'N\', \'C\').\n" \
  "    {tb.key_hsh[0..nkeys-1]} = (int) the hash value of each key.\n" \
  "    {tb.key_bix[0..nkeys-1]} = (int) the index of each key\'s bucket among the VISIBLE bucket entries.\n" \
  "\n" \
  "    {tb.buc_hsh[0..nbucs-1]} = (int) the hash (index) of each VISIBLE bucket, or -1 if none.\n" \
  "    {tb.buc_kix[0..nbucs-1]} = (int) the index of a key associated to the bucket, or -1 if vacant.\n" \
  "    {tb.buc_hsh_sty[0..nbucs-1]} = the style of each hash box (\'N\', \'U\', \'C\') or \':\' for a vdots box.\n" \
  "    {tb.buc_oix[0..nbucs-1]} = (int) the index of the ovflow entry box which the bucket points to, or -1 if none.\n" \
  "\n" \
  "    {tb.buc_has_key} = (bool) 1 iff buckets have keys.\n" \
  "    {tb.buc_has_val} = (bool) 1 iff buckets have values.\n" \
  "    {tb.buc_has_ptr} = (bool) 1 iff buckets have pointers.\n" \
  "    {tb.has_buc_box} = (bool) 1 iff bucket column has bucket boxes, 0 iff has only the hashes.\n" \
  "\n" \
  "    {tb.ovf_kix[0..novfs-1]} = (int) the index of the key which is stored in each overflow entry, or -1 if vacant.\n" \
  "\n" \
  "    {tb.ovf_has_key} = (bool) 1 iff overflow entries have keys.\n" \
  "    {tb.ovf_has_val} = (bool) 1 iff overflow entries have values.\n" \
  "    {tb.ovf_has_ptr} = (bool) 1 iff overflow entries have pointers.\n" \
  "\n" \
  "  For \'SP\' type tables, {tb.buc_kix[j]} is the index of the key which is" \
  " actualy stored in the bucket, which may or may not hash into it.  For" \
  " all other table types, {tb.buc_kix[j]} is one of the entries that hashed into that" \
  " bucket.  The meaning of {tb.buc_kix[j]} is independent of whether the bucket elements" \
  " are actual entries or just links or."
  
  def __init__(tb, op) :

    assert(op.nkeys >= 3)
    assert(op.nkeys <= 5)

    tb.choose_keys_and_hashes(op)
    tb.choose_and_assign_buckets(op)
    tb.gather_overflow_entries(op)
    
    # Decide what goes into the buckets:
    tb.buc_has_key = op.keys and (not op.links)
    tb.buc_has_val = op.values and (not op.links)
    if op.collisions :
      if op.keys :
        # Figure showing a dynamic set or dynamic table with collisions:
        tb.buc_has_ptr = op.links or (op.overflow == 'LL')
      else :
        # Figure makes no sense as a table or set.
        # It must show a hash function with collisions:
        tb.buc_has_ptr = 0
    else :
       if op.keys or op.values or op.links :
         # Figure shows a collision-less table or dynamic set:
         tb.buc_has_ptr = op.links
       else :
         # Figure shows a collision-less hash function:
         tb.buc_has_ptr = 0
    tb.has_buc_box = tb.buc_has_key or tb.buc_has_val or tb.buc_has_ptr
    
    # Decide what goes into the overflow records:
    if tb.novfs == 0 :
      # There is no overfow block:
      tb.ovf_has_key = 0
      tb.ovf_has_val = 0
      tb.ovf_has_ptr = 0
    else :  
      assert(op.links or (op.collisions and (op.overflow != 'SP')))
      tb.ovf_has_key = op.keys
      tb.ovf_has_val = op.values
      tb.ovf_has_ptr = op.collisions and (op.overflow == 'LL')
        
    ################################################################

  def choose_keys_and_hashes(tb, op) :
    "Chooses the keys and their hashes, as requested in {op}.\n" \
    "\n" \
    "  Sets {tb.nkeys} to {op.nkeys}, and fills the arrays that describe the" \
    " keys column, namely {tb.key_str[i]}, {tb.key_val[i]}, and" \
    " {tb.key_hsh[i]} for {i} in {0..tb.nkeys-1}.\n"

    sys.stderr.write("entering {choose_keys_and_hashes}\n")
    
    # Fill {tb.key_str,tb.key_val} with 5 keys:
    tb.key_str = [ 'S0', 'S1', 'S2',  'S3', 'S4' ]
    tb.val_str = [ 'V0', 'V1', 'V2',  'V3', 'V4'  ]
    tb.nkeys = len(tb.key_str)

    # Choose the max hash value {tb.max_hsh}:
    if op.sparse :
      if op.nkeys <= 4 :
        tb.max_hsh = 15
      else:
        tb.max_hsh = 255
    else :
      if op.collisions :
        tb.max_hsh = int(tb.nkeys - 2)
      else :
        tb.max_hsh = int(tb.nkeys - 1)

    # Hashes of the keys and their positions:
    if tb.max_hsh <= op.nkeys :
      tb.key_hsh = [ 1, 0, 4, 3, 2 ]
    elif tb.max_hsh == 15 : 
      tb.key_hsh = [ 02, 01, 04, 14, 03 ]
    else :
      tb.key_hsh = [ 152, 001, 254, 154, 153 ]

    if op.collisions :
      # Make "Sandra Dee" collide with "John Smith":
      tb.key_hsh[3] = tb.key_hsh[0]

    # Eliminate excess keys:
    if op.nkeys <= 4 :
      # Delete "Ted Baker":
      tb.exclude_candidate_key(op, 4)
    if op.nkeys <= 3 :
      # Delete "Sam Doe":
      tb.exclude_candidate_key(op, 2)

    sys.stderr.write("tb.key_str = %r\n" % tb.key_str)
    sys.stderr.write("tb.val_str = %r\n" % tb.val_str)
    sys.stderr.write("tb.key_hsh = %r\n" % tb.key_hsh)
    sys.stderr.write("tb.max_hsh = %r\n" % tb.max_hsh)
    assert(tb.nkeys == op.nkeys)
    ################################################################

  def exclude_candidate_key(tb, op, k) :
    "Excludes a key from the key tables.\n" \
    "\n" \
    "  Excludes key number {k} from {tb.key_str[],tb.val_str[],tb.key_hsh[]}.  If {op.sparse}" \
    " is false, adjusts {tb.key_hsh[]} so that it remains surjective after the deletion."
    h = tb.key_hsh[k]
    tb.key_str[k:k+1] = []
    tb.val_str[k:k+1] = []
    tb.key_hsh[k:k+1] = []
    tb.nkeys = tb.nkeys - 1
    if op.sparse : return
    for i in range(tb.nkeys) :
      if tb.key_hsh[i] == h :
        # Some other key maps to the hash {h}, so no adjustment is needed.
        return
    # Eliminate {h} from the hash function's range:
    for i in range(tb.nkeys) :
      if tb.key_hsh[i] > h :
        tb.key_hsh[i] = tb.key_hsh[i] - 1
    tb.max_hsh = tb.max_hsh - 1

  def choose_and_assign_buckets(tb, op) :
    "Chooses which hashes and buckets to show, and assigns them to the keys.\n" \
    "\n" \
    "  Defines {tb.nbucs}, the number of slots to show in the hash/bucket" \
    " column (including the \"vdots\" slots).  Sets {tb.buc_hsh[j]} to the" \
    " hash value to be shown for the slot (or -1 for \"vdots\")\n" \
    "\n" \
    "  Simulates the hash table algorithm for the key" \
    " hashes {tb.key_hsh[0..tb.nkeys-1]}.\n" \
    "\n" \
    "  For each key index {i}, sets {tb.key_bix[i]} to the index of the bucket where the" \
    " key hashes to, and {tb.key.sty[i]} to the style to use for the key ('N' or 'C').\n" \
    "\n" \
    "  For each bucket index {j}, sets {tb.buc_kix[j]} to the index of the key" \
    " that is stored in the bucket (if any).  Also sets {tb.buc_hsh_sty[j]} to" \
    " the style to use for the bucket ('U', 'C', 'N', or ':').\n" \
    "\n" \
    "  The indices {j} are indices into the bucket-related arrays, such" \
    " as {tb.buc_hsh[]}, which are a compressed subset of the actual table buckets."
    
    sys.stderr.write("entering {choose_and_assign_buckets}\n")
    
    # Initially assume that all buckets are visible:
    tb.buc_hsh = []
    tb.nbucs = tb.max_hsh + 1
    for h in range(tb.nbucs) :
      tb.buc_hsh[h:h] = [ h ]
    
    # Initialize {tb.key_bix[i],tb.key.sty[i],tb.buc_kix[j],tb.buc_hsh_sty[j]} with all nulls:
    tb.key_sty =     [ 'N' ]*tb.nkeys
    tb.key_bix =     [ -1  ]*tb.nkeys
    tb.buc_kix =     [ -1  ]*tb.nbucs
    tb.buc_hsh_sty = [ 'U' ]*tb.nbucs
 
    # Assign buckets to keys:
    for i in range(tb.nkeys) :
      tb.assign_bucket_to_key(i)

    # Set {bvs[h]} to 1 iff bucket {h} of the table is to be shown:
    bvs = [ 0 ] * (tb.max_hsh + 1) # Initially all invisible.
    for h in range(tb.nbucs) :
      i = tb.buc_kix[h]
      if i >= 0 :
        # Mark bucket {h} and its two neighbors as visible:
        assert(i < tb.nkeys)
        bvs[h] = 1;
        if h > 0 : bvs[h-1] = 1
        if h < tb.max_hsh : bvs[h+1] = 1
    # The first and last buckets must be shown in any case:
    bvs[0] = 1
    bvs[tb.max_hsh] = 1

    sys.stderr.write("--- before squeezing ---\n")
    sys.stderr.write("tb.key_bix     = %r\n" % tb.key_bix)
    sys.stderr.write("tb.buc_hsh     = %r\n" % tb.buc_hsh)
    sys.stderr.write("tb.buc_hsh_sty = %r\n" % tb.buc_hsh_sty)
    sys.stderr.write("tb.buc_kix     = %r\n" % tb.buc_kix)

    # Now squeeze the bucket column entries, set {tb.buc_hsh_sty}:
    h = 0            # Next hash to consider
    tb.nbucs = 0     # Number of squeezed buckets
    while h <= tb.max_hsh :
      if (h < tb.max_hsh) and bvs[h+1] :
        # No use to omit a single slot:
        bvs[h] = 1
      if bvs[h] :
        # Slot {h} is to be shown:
        sys.stderr.write("relocating slot %d (kix = %d) to slot %d\n" % (h,tb.buc_kix[h],tb.nbucs))
        # Fix all ket-to-buck pointers:
        for i in range(tb.nkeys) :
          if tb.key_bix[i] == h :
            # Relocate the key-to-bucket pointer:
            sys.stderr.write("  key %d was hashed to bucket %d, now %d\n" % (i,tb.key_bix[i],tb.nbucs))
            tb.key_bix[i] = tb.nbucs
        # Relocate bucket {h} to bucket {tb.nbucs}, increment {h}:
        tb.buc_hsh[tb.nbucs] = h
        tb.buc_hsh_sty[tb.nbucs] = tb.buc_hsh_sty[h]
        tb.buc_kix[tb.nbucs] = tb.buc_kix[h]
        h = h + 1
      else :
        # {h} is the start of 2 or more slots that are not relevant:
        # Append -1 to the list, skip all invisible buckets:
        sys.stderr.write("slot %d starts a gap; squeezed to slot %d\n" % (h,tb.nbucs))
        tb.buc_hsh[tb.nbucs] = -1
        tb.buc_hsh_sty[tb.nbucs] = ':'
        tb.buc_kix[tb.nbucs] = -1
        while (h <= tb.max_hsh) and not bvs[h] : h = h + 1
      tb.nbucs = tb.nbucs + 1

    # Truncate the bucket arrays:
    tb.buc_hsh[tb.nbucs:len(tb.buc_hsh)] = []
    tb.buc_kix[tb.nbucs:len(tb.buc_kix)] = []
    tb.buc_hsh_sty[tb.nbucs:len(tb.buc_hsh_sty)] = []

    sys.stderr.write("--- after squeezing ---\n")
    sys.stderr.write("tb.key_bix     = %r\n" % tb.key_bix)
    sys.stderr.write("tb.buc_hsh     = %r\n" % tb.buc_hsh)
    sys.stderr.write("tb.buc_hsh_sty = %r\n" % tb.buc_hsh_sty)
    sys.stderr.write("tb.buc_kix     = %r\n" % tb.buc_kix)
    assert(tb.nbucs == len(tb.buc_hsh))
    ################################################################

  def gather_overflow_entries(tb, op) :
    "Gathers the overflow entries of each bucket, and sets bucket-overflow pointers.\n" \
    "\n" \
    "  Sets sets {tb.novfs} to the number of entries to show in the overflow column.\n" \
    "\n" \
    "  For each overflow entry {k}, sets {tb.ovf_kix[k]} to the index of the key" \
    " that is stored in that entry, or -1 if none.  Also sets {tb.ovf.pix[k]} to" \
    " the indes {k'} of the next slot in the bucket's chain, or -1 if none.\n" \
    "\n" \
    "  For each bucket index {j}, sets {tb.buc_oix[j]} to the index of the overflow" \
    " slot where the first entry of that bucket is stored, or -1 if none." \
    " increments"
    tb.buc_oix =     [ -1  ]*tb.nbucs
    tb.novfs = 0
    tb.ovf_kix = [ ]
    tb.ovf_pix = [ ]
    for j in range(tb.nbucs) :
      if tb.buc_hsh[j] == -1 :
        tb.buc_hsh_sty[j] = ':'
      tb.gather_bucket_overflow(j)
    ################################################################

  def assign_bucket_to_key(tb,i) :
    "Finds the bucket where key number {i} hashes to and its the hash arrow.\n" \
    "\n" \
    "  Finds the index {bix} of the bucket where key number {i} hashes to.  Sets" \
    " {tb.key_bix[i]} to {bix}.  If no one has hashed or is living there yet, sets" \
    " {tb.buc_kix[bix]} to {i}; otherwise leaves {tb.buc_kix[bix]} unchanged" \
    " and sets the styles of the bucket and of the two keys to 'C'.\n" \
    "\n" \
    "   If the table uses sequential probing and the bucket {bix} is occupied,\n" \
    " finds the next free slot {bsx} and stores the key there, setting {tb.buc_kix[bsx]} to {i}" \
    "\n" \
    " If key {i} has hash -1, returns -1."

    sys.stderr.write("key %d = %s hash = %d\n" % (i, tb.key_str[i], tb.key_hsh[i]))
    if tb.key_hsh[i] == -1 :
      # A hashless key?
      tb.key_sty[i] = 'C';
      tb.key_bix[i] = -1
      sys.stderr.write("  hashless key\n")
    else :
      # Find the index {tb.key_bix[i]} of bucket where this key is hashed into:
      bix = -1
      for j in range(tb.nbucs) :
        if tb.key_hsh[i] == tb.buc_hsh[j] : bix = j
      sys.stderr.write("  hashed to slot %d = %d\n" % (bix, tb.buc_kix[bix]))
      assert (bix != -1) # The hash of every key must be visible.
      assert (tb.buc_hsh[bix] == tb.key_hsh[i]) # Paranoia.
      # Remember the bucket where the key is hashed to:
      tb.key_bix[i] = bix
      # Update the key and bucket styles, then set {bsx} to the
      # index of the bucket where the entry can be stored, or to -1:
      if tb.buc_kix[bix] == -1 :
        # No key has hashed into this bucket yet.
        sys.stderr.write("  first hash to this slot\n")
        tb.buc_kix[bix] = i
        tb.buc_hsh_sty[bix] = 'N'
      else :
        # Some other key was previously hashed to this bucket.
        sys.stderr.write("  hashed slot %d is occupied by key %d = %s\n" % (bix, tb.buc_kix[bix], tb.key_str[tb.buc_kix[bix]]))
        # Flag the collision:
        tb.key_sty[i] = 'C';
        tb.key_sty[tb.buc_kix[bix]] = 'C';
        tb.buc_hsh_sty[bix] = 'C'
        if op.overflow == 'SP' :
          # Must assign the next available bucket to key {i}.
          bsx = (bix + 1) % tb.nbucs
          while (bsx < tb.nbucs) and (bsx != bix) :
            # Try allocating to bucket {bsx}:
            sys.stderr.write("    trying slot %d = %d\n" % (bsx, tb.buc_kix[bsx]))
            assert (tb.buc_hsh[bsx] != -1) # Cannot store into invisible buckets.
            if tb.buc_kix[bsx] == -1 : break
            tb.buc_hsh_sty[bsx] = 'C'
            bsx = (bsx + 1) % tb.nbucs
          assert (bsx != bix)
          tb.buc_kix[bsx] = i
          tb.buc_hsh_sty[bsx] = 'N'
          sys.stderr.write("  finally assigned to slot %d hash = %d\n" % (bsx, tb.buc_hsh[bsx]))
    ################################################################

  def gather_bucket_overflow(tb,j) :
    "Allocates the overflow records of bucket {j}.\n" \
    "\n" \
    "  If the table does not store keys nor values, there is no point in" \
    " having a overflow column.\n" \
    "\n" \
    "  For \'LL\' type tables, gathers all keys that hash into bucket {j}" \
    " and allocates records in the overflow column.  If buckets are not" \
    " links, excludes the first of those entries.\n" \
    "\n" \
    "  For \'SP\' type tables, if the buckets are just links, allocates" \
    " the record coresponding to bucket {j} in the overflow" \
    " column.  If buckets are whole entries, does nothing.\n" \
    "\n" \
    "  In any case, sets {tb.buc_oix[j],tb.ovf_kix[k],tb.ovf.pix[k]} and" \
    " increments {tb.novfs} as appropriate."

    # Default case:
    tb.buc_oix[j] = -1
    if tb.buc_kix[j] == -1 : return

    if not (op.keys or op.values) :
      # There is no point in having overflow records:
      return
      
    if op.overflow == 'SP' :
      if op.links :
        # Make link to single entry:
        tb.buc_oix[j] = tb.alloc_overflow_record(tb.buc_kix[j])
      else :
        # Nothing to gather:
        return
    elif op.overflow == 'LL' :
      # Gather all keys that hash to this bucket:
      for i in range(tb.nkeys) :
        if tb.key_bix[i] == j and (op.links or (tb.buc_kix[j] != i)) :
          # This key should go to overflow:
          eix = tb.alloc_overflow_record(i)
          if (tb.buc_oix[j] == -1) :
            # First overflow of this bucket:
            tb.buc_oix[j] = eix
          else :
            # Append overflow record to previous record:
              tb.ovf_pix[eix-1] = eix
    else :
      assert(0) # Should have caught this when parsing the command args.
    ################################################################
    
  def alloc_overflow_record(tb,i) :
    "Allocates a record for key number {i} in the overflow column.\n" \
    "\n" \
    "  Allocates a record for key number {i} at the next available" \
    " position {k = tb.novfs} in the overflow column.  Sets" \
    " {tb.ovf_kix[k]} to {i}, {tb.ovf_pix[k]} to -1, and" \
    " increments {tb.novfs}.  Returns {k}."
    k = tb.novfs
    tb.novfs = tb.novfs + 1
    tb.ovf_kix[k:k] = [ i ]
    tb.ovf_pix[k:k] = [ -1 ]
    return k
    ################################################################
  
  ################################################################

class Dimensions :
  def __init__(dim, op,tb) :

    # All Y positions are relative to the figure minus headers and margins.
    
    # Number of digits in hash value:
    if tb.max_hsh < 10 :
      dim.hsh_ndg = 1  # Number of digits in hash value.
    elif tb.max_hsh < 100 :
      dim.hsh_ndg = 2  # Number of digits in hash value.
    elif tb.max_hsh < 1000 :
      dim.hsh_ndg = 3  # Number of digits in hash value.
    else :
      assert(0)

    # --- Determine widths of main items ---

    # Determine the width of the key, value, and pointer boxes:
    dim.key_box_wx = 30    # X size of key box.
    dim.val_box_wx = 80    # X size of value box.
    dim.ptr_box_wx = 20    # X size of pointer box.

    # Determine the width of the function box:
    if op.funcbox :
      dim.fun_box_wx = 70  # X size of hash function box (if visible).
    else:
      dim.fun_box_wx = 30  # X size of hash function box (if invisible).

    # Determine the width of the hashval box:
    dim.hsh_box_wx = 10 + 10*dim.hsh_ndg  # X size of hashval box.
    
    # Determine the width of the bucket box:
    dim.buc_box_wx = 0
    if tb.buc_has_key :
      dim.buc_box_wx = dim.buc_box_wx + dim.key_box_wx
    if tb.buc_has_val :
      dim.buc_box_wx = dim.buc_box_wx + dim.val_box_wx
    if tb.buc_has_ptr :
      dim.buc_box_wx = dim.buc_box_wx + dim.ptr_box_wx
    assert((tb.has_buc_box == 0) == (dim.buc_box_wx == 0))

    # Determine the width of the overflow entry box:
    dim.ovf_box_wx = 0
    if tb.ovf_has_key :
      dim.ovf_box_wx = dim.ovf_box_wx + dim.key_box_wx
    if tb.ovf_has_val :
      dim.ovf_box_wx = dim.ovf_box_wx + dim.val_box_wx
    if tb.ovf_has_ptr :
      dim.ovf_box_wx = dim.ovf_box_wx + dim.ptr_box_wx
    assert((tb.novfs == 0) == (dim.ovf_box_wx == 0))
    
    # --- Determine th X spacings between main items ---

    # This should be zero if {dim.buc_box_wx} is zero:
    dim.buc_col_sx = 0   # X spacing between hashes column and buckets column.

    # Padding needed after key box:
    key_pad_x = 10

    # Padding needed around function box:
    if op.funcbox :
      # Need padding for column header:
      fun_pad_x = max(80 - dim.fun_box_wx, 0) / 2
    else :
      # Minimal padding:
      fun_pad_x = 10

    # Padding needed around hash+bucket column (for header):
    hbu_pad_x = max(90 - (dim.hsh_box_wx + dim.buc_col_sx + dim.buc_box_wx), 20)/2
    
    # Padding needed before overflow column (for header):
    ovf_pad_x = max(90 - (dim.ovf_box_wx), 20)/2
    
    # X spacing between key boxes and function box:
    dim.fun_col_sx = key_pad_x + fun_pad_x 

    # X spacing between function box and hash box:
    dim.hsh_col_sx = fun_pad_x + hbu_pad_x

    # Choose the X spacing between bucket box and the overflow boxes.
    # This should be zero if {dim.ovf_box_wx} is zero:
    if dim.ovf_box_wx == 0 :
      dim.ovf_col_sx = 0 
    else :
      dim.ovf_col_sx = hbu_pad_x + ovf_pad_x

    # X size of diagram proper (minus margins):
    dim.diag_wx = \
      dim.key_box_wx + \
      dim.fun_col_sx + dim.fun_box_wx + \
      dim.hsh_col_sx + dim.hsh_box_wx + \
      dim.buc_col_sx + dim.buc_box_wx + \
      dim.ovf_col_sx + dim.ovf_box_wx

    # Find padding needed for rightmost column with title:
    if tb.novfs > 0 :
      last_pad_x = ovf_pad_x + 10
    else :
      last_pad_x = hbu_pad_x + 10

    dim.diag_wx = dim.diag_wx + last_pad_x 

    # --- Determine item and column heights and Y spacings ---
    
    dim.box_wy = 20        # Y size of all text boxes.

    dim.key_col_sy = 20    # Y spacing between boxes in key column.

    # Choose {dim.ovf_col_sy}, the Y spacing between boxes in overflow entry column:
    if tb.novfs < 2 :
      dim.ovf_col_sy = dim.key_col_sy # Not used, but just in case...
    else :
      # Try to use the whole spce available:
      key_tmp_wy =tb.nkeys*(dim.box_wy + dim.key_col_sy)
      buc_tmp_wy =tb.nbucs*dim.box_wy
      tmp_wy =  max(key_tmp_wy, buc_tmp_wy)
      tmp_sy = (tmp_wy - tb.novfs*dim.box_wy)/(tb.novfs + 1)
      if tmp_sy < 10 :
        dim.ovf_col_sy = 10
      else :
        dim.ovf_col_sy = 10*int((tmp_sy + 9)/10)

    # Compute minimum column heights: keys, function, hashes&buckets, overflow:
    key_col_raw_wy = tb.nkeys*dim.box_wy + (tb.nkeys - 1)*dim.key_col_sy
    hsh_col_raw_wy = tb.nbucs*dim.box_wy
    fun_col_raw_wy = max(key_col_raw_wy, hsh_col_raw_wy)
    ovf_col_raw_wy = tb.novfs*dim.box_wy + (tb.novfs - 1)*dim.ovf_col_sy

    dim.fun_box_wy = fun_col_raw_wy  # Y size of function box.

    # Y size of diagram proper (minus margins and column headers):
    dim.diag_wy = max(fun_col_raw_wy, key_col_raw_wy, hsh_col_raw_wy, ovf_col_raw_wy) 

    # Top Y positions (relative to the figure minus headers and margins):
    dim.fun_col_ty = (dim.diag_wy - fun_col_raw_wy)/2  # Y position of function box.
    dim.key_col_ty = (dim.diag_wy - key_col_raw_wy)/2  # Y position of topmost key box.
    dim.hsh_col_ty = (dim.diag_wy - hsh_col_raw_wy)/2  # Y position of first hash value box.
    dim.buc_col_ty = dim.hsh_col_ty     # Y position of first bucket box.
    dim.ovf_col_ty = (dim.diag_wy - ovf_col_raw_wy)/2  # Y position of first overflow entry box.
    
    # Column header dimensions:
    dim.tit_wy = 20  # Baseline spacing for column headers.
    dim.tit_sy = 10  # Spacing between bottom of headers and top of diagram proper.

    dim.mrg_wx = 10  # X width of figure margin.
    dim.mrg_wy = 10  # Y width of figure margin.

    # Total X and Y size of figure:
    dim.fig_wx = \
      dim.mrg_wx + \
      dim.diag_wx + \
      dim.mrg_wx

    dim.fig_wy = \
      dim.mrg_wy + \
      2*dim.tit_wy +  dim.tit_sy + \
      dim.diag_wy + \
      dim.mrg_wy

    # Overall scale (after all dimensions):
    dim.scale = 1.0
    ################################################################

  ################################################################
  
def output_figure(op) :
  "Writes the figure to {stdout}."
  "\n" \
  "  Expects an {Options} instance {op}."

  # Create the table:
  tb = HashTable(op)

  # Computes the sizes of things:
  dim = Dimensions(op,tb)

  output_figure_preamble(op,tb,dim)
  sys.stdout.write('\n')
  output_figure_obj_defs(op,tb,dim)
  sys.stdout.write('\n')
  output_figure_body(op,tb,dim)
  sys.stdout.write('\n')
  output_figure_postamble(op,tb,dim)
  sys.stderr.write("done.\n")
  ################################################################
  
def output_figure_preamble(op,tb,dim) :
  "Writes the SVG preamble to {stdout}."
  
  sys.stdout.write( \
    '<?xml version="1.0" encoding="UTF-8" standalone="no"?>\n' \
    '<!DOCTYPE svg PUBLIC "-//W3C//DTD SVG 1.1//EN" "http://www.w3.org/Graphics/SVG/1.1/DTD/svg11.dtd">\n' \
    '<!-- Created on '+ date.isoformat(date.today()) +' by Jorge Stolfi with the script make-hash-table-figure -->\n' \
    '\n' \
    '<svg\n' \
    '  xmlns="http://www.w3.org/2000/svg"\n' \
    '  xmlns:xlink="http://www.w3.org/1999/xlink"\n' \
    '  width="'+ dts(dim.scale*dim.fig_wx) +'"\n' \
    '  height="'+ dts(dim.scale*dim.fig_wy) +'"\n' \
    '  id="fig"\n' \
    '  stroke-width="1px"\n' \
    '  stroke-linejoin="round"\n' \
    '  stroke-opacity="1"\n' \
    '  stroke-linecap="round"\n' \
    '  fill-opacity="1"\n' \
    '  fill-rule="evenodd"\n' \
    '  font-family="Bitstream Courier"\n' \
    '  font-style="normal"\n' \
    '  font-weight="normal"\n' \
    '  pagecolor="#ffff00"\n' \
    '  pageopacity="0.0">\n' \
  )
  sys.stdout.write('\n')
  if (op.back) :
    sys.stdout.write( \
      '    <!-- Rectangle to test the figure size -->\n' \
      '    <rect x="000" y="000" width="'+ dts(dim.scale*dim.fig_wx) +'" height="'+ dts(dim.scale*dim.fig_wy) +'"' \
             ' stroke="#000000" fill="#cccccc"' \
             ' />\n' \
    )
  sys.stdout.write('\n')

  # Scale everything and position the diagram:
  diag_dx = dim.mrg_wx
  diag_dy = dim.mrg_wy + 2*dim.tit_wy + dim.tit_sy
  sys.stdout.write( \
    '  <g\n' \
    '    font-size="12px"\n' \
    '    transform="scale('+ dts(dim.scale)+ ') translate('+ dts(diag_dx) + ','+ dts(diag_dy) + ')"\n' \
    '  >\n' \
  )
  ################################################################

def output_figure_obj_defs(op,tb,dim) :
  "Writes the main object definitions to {stdout}."

  sys.stdout.write( \
    '  <defs>\n' \
    '    <!-- Start marker for non-null pointers: -->\n' \
    '    <marker id="linkdot_N" viewBox="0 0 8 8" refX="4" refY="4" markerWidth="8" markerHeight="8" orient="auto">\n' \
    '      <circle cx="4" cy="4" r="3" stroke="#000000" fill="#000000" />\n' \
    '    </marker>\n' \
    '    <!-- Start marker for null pointers: -->\n' \
    '    <marker id="linkdot_U" viewBox="0 0 8 8" refX="4" refY="4" markerWidth="8" markerHeight="8" orient="auto">\n' \
    '      <line x1="1" y1="1" x2="7" y2="7" stroke="#000000" />\n' \
    '      <line x1="1" y1="7" x2="7" y2="1" stroke="#000000" />\n' \
    '    </marker>\n' \
    '\n' \
    '    <!-- Tip for arrows: -->\n' \
    '    <marker id="arrowtip_N" viewBox="0 0 14 8" refX="13" refY="4" markerWidth="14" markerHeight="8" orient="auto">\n' \
    '      <polygon points="1,4  1,1  13,4  1,7" stroke="#000000" fill="#000000" />\n' \
    '    </marker>\n' \
    '    <!-- Tip for highlighted arrows: -->\n' \
    '    <marker id="arrowtip_C" viewBox="0 0 14 8" refX="13" refY="4" markerWidth="14" markerHeight="8" orient="auto">\n' \
    '      <polygon points="1,4  1,1  13,4  1,7" stroke="#aaaaaa" fill="#aaaaaa" />\n' \
    '    </marker>\n' \
    '\n' \
    '    <!-- Key box in input column, normal: -->\n' \
    '    <rect id="key_box_N"   y="0" x="0" width="'+ dts(dim.key_box_wx) +'" height="'+ dts(dim.box_wy) +'"' \
          ' fill="none" stroke-width="0px" stroke="none"' \
          ' />\n' \
    '    <!-- Key box in input column, highlighted : -->\n' \
    '    <rect id="key_box_C"   y="0" x="0" width="'+ dts(dim.key_box_wx) +'" height="'+ dts(dim.box_wy) +'"' \
          ' fill="none" stroke-width="0px" stroke="none"' \
          ' />\n' \
    '    <!-- Key box in bucket or overflow columns, normal: -->\n' \
    '    <rect id="key_box_E"   y="0" x="0" width="'+ dts(dim.key_box_wx) +'" height="'+ dts(dim.box_wy) +'"' \
          ' fill="none" stroke="#000000"' \
          ' />\n' \
    '    <!-- Key box in bucket or overflow columns, vacant: -->\n' \
    '    <rect id="key_box_U"   y="0" x="0" width="'+ dts(dim.key_box_wx) +'" height="'+ dts(dim.box_wy) +'"' \
          ' fill="#ddeedd" stroke="#000000"' \
          ' />\n' \
    '\n' \
    '    <!-- Value box in bucket or overflow columns, occupied: -->\n' \
    '    <rect id="val_box_E"   y="0" x="0" width="'+ dts(dim.val_box_wx) +'" height="'+ dts(dim.box_wy) +'"' \
          ' fill="none" stroke="#000000"' \
          ' />\n' \
    '    <!-- Value box in bucket or overflow columns, vacant: -->\n' \
    '    <rect id="val_box_U"   y="0" x="0" width="'+ dts(dim.val_box_wx) +'" height="'+ dts(dim.box_wy) +'"' \
          ' fill="none" stroke="#000000"' \
          ' />\n' \
    '\n' \
    '    <!-- Pointer box in bucket or overflow columns, used and non-null: -->\n' \
    '    <rect id="ptr_box_E"   y="0" x="0" width="'+ dts(dim.ptr_box_wx) +'" height="'+ dts(dim.box_wy) +'"' \
          ' fill="none" stroke="#000000"' \
          ' />\n' \
    '    <!-- Pointer box in bucket or overflow columns, null/vacant: -->\n' \
    '    <rect id="ptr_box_U"   y="0" x="0" width="'+ dts(dim.ptr_box_wx) +'" height="'+ dts(dim.box_wy) +'"' \
          ' fill="none" stroke="#000000"' \
          ' />\n' \
    '\n' \
    '    <!-- Background for hash value, unused: -->\n' \
    '    <rect id="hsh_box_U" x="3" y="1" width="'+ dts(dim.hsh_box_wx-6) +'" height="'+ dts(dim.box_wy-2) +'"' \
          ' fill="#f0f0f0" stroke-width="0px" stroke="none"' \
          ' />\n' \
    '    <!-- Background for hash value, used: -->\n' \
    '    <rect id="hsh_box_N" x="3" y="1" width="'+ dts(dim.hsh_box_wx-6) +'" height="'+ dts(dim.box_wy-2) +'"' \
         ' fill="#cccccc" stroke-width="0px" stroke="none"' \
         ' />\n' \
    '    <!-- Background for hash value, highlighted: -->\n' \
    '    <rect id="hsh_box_C" x="3" y="1" width="'+ dts(dim.hsh_box_wx-6) +'" height="'+ dts(dim.box_wy-2) +'"' \
         ' fill="#cccccc" stroke-width="0px" stroke="none"' \
         ' />\n' \
    '\n' \
    '    <!-- Vertical dots: -->\n' \
    '    <g id="vdots">\n' \
    '      <rect x="0" y="06" width="2" height="2" />\n' \
    '      <rect x="0" y="12" width="2" height="2" />\n' \
    '    </g>\n' \
    ' </defs>\n' \
  )
  ################################################################

def output_figure_body(op,tb,dim) :
  "Writes the body of the figure to {stdout}."

  # All dimensions computed here are relative to the figure body (excluding titles and left margin).

  # X positions and widths of the major sub-blocks:
  key_fun_block_dx = 0
  key_fun_block_wx = dim.key_box_wx + dim.fun_col_sx + dim.fun_box_wx
  
  hsh_buc_block_dx = key_fun_block_dx + key_fun_block_wx + dim.hsh_col_sx
  hsh_buc_block_wx = dim.hsh_box_wx + dim.buc_col_sx + dim.buc_box_wx
  
  ovf_block_dx = hsh_buc_block_dx + hsh_buc_block_wx + dim.ovf_col_sx
  ovf_block_wx = dim.ovf_box_wx

  # Key boxes, hash function box, and hash function arrows:
  sys.stdout.write( \
    '    <!-- Keys and hash function -->\n' \
    '    <g transform="translate('+ dts(key_fun_block_dx) +',000)"\n' \
    '      text-anchor="middle"\n' \
    '    >\n' \
  )
  sys.stdout.write('\n')
  output_key_fun_block(op,tb,dim)
  sys.stdout.write('\n')
  sys.stdout.write( \
    '    </g>\n' \
  )

  sys.stdout.write('\n')

  # Hash values and bucket array:
  sys.stdout.write( \
    '    <!-- Hash values and bucket array -->\n' \
    '    <g transform="translate('+ dts(hsh_buc_block_dx) + ',000)"\n' \
    '      text-anchor="middle"\n' \
    '    >\n' \
  )
  ovf_dx = ovf_block_dx - hsh_buc_block_dx # Displacment of overflow entries col relative to hashes col.
  sys.stdout.write('\n')
  output_hsh_buc_block(op,tb,dim, ovf_dx)
  sys.stdout.write('\n')
  sys.stdout.write( \
    '    </g>\n' \
  )
  
  sys.stdout.write('\n')

  if tb.novfs > 0 :
  # Overflow entries:
    sys.stdout.write( \
      '    <!-- Hash values and bucket array -->\n' \
      '    <g transform="translate('+ dts(ovf_block_dx) + ',000)"\n' \
      '      text-anchor="middle"\n' \
      '    >\n' \
    )
    sys.stdout.write('\n')
    output_ovf_block(op,tb,dim)
    sys.stdout.write('\n')
    sys.stdout.write( \
      '    </g>\n' \
    )
  ################################################################
  
def output_key_fun_block(op,tb,dim) :
  "Writes the key and hash-function block to {stdout}."

  # All dimensions computed here are relative to the hash function block.
  # Assumes that the top of the bucket block is aligned with the top of the key block.

  # baselines of the two header lines:
  tit_dy_top = - dim.tit_sy - dim.tit_wy
  tit_dy_bot = - dim.tit_sy
  
  # X positions of the key and function boxes:
  key_box_dx = 0
  key_box_tit_ax = key_box_dx + dim.key_box_wx/2

  fun_box_dx = key_box_dx + dim.key_box_wx + dim.fun_col_sx
  fun_box_tit_ax = fun_box_dx + dim.fun_box_wx/2  # X position of function box title's anchor point.

  if op.funcbox :
    # Title for function box:
    sys.stdout.write( \
      '      <text x="'+ dts(fun_box_tit_ax) +'" y="'+ dts(tit_dy_top) +'" font-size="15px"' \
              ' font-weight="bold" fill="#000000" stroke-width="0px" stroke="none">' \
              ' hash ' \
              ' </text>\n' \
      '      <text x="'+ dts(fun_box_tit_ax) +'" y="'+ dts(tit_dy_bot) +'" font-size="15px"' \
              ' font-weight="bold" fill="#000000" stroke-width="0px" stroke="none">' \
              ' function' \
              ' </text>\n' \
    )
    sys.stdout.write('\n')

    # Function box (must paint it first to get correct layer depth):
    fun_ty = dim.fun_col_ty
    sys.stdout.write( \
      '      <rect x="'+ dts(fun_box_dx) +'" y="'+ dts(fun_ty) +'"' \
              ' width="'+ dts(dim.fun_box_wx) +'" height="'+ dts(dim.fun_box_wy) +'"' \
              ' fill="#aaeecc" stroke-width="0px" stroke="none"' \
              ' />\n' \
    )
    sys.stdout.write('\n')
  
  # Title for column of key boxes:
  sys.stdout.write( \
    '      <text x="'+ dts(key_box_tit_ax) +'" y="'+ dts(tit_dy_bot) +'" font-size="15px"' \
            ' font-weight="bold" fill="#000000" stroke-width="0px" stroke="none">' \
            ' \n' \
            ' </text>\n' \
  )
  sys.stdout.write('\n')

  # Column of key boxes:
  key_ty = dim.key_col_ty  # Y position of next key box.
  for i in range(tb.nkeys) :
    # Compute top Y {hsh_ty} of corresponding hash value box:
    hsh_ty = dim.hsh_col_ty + dim.box_wy*tb.key_bix[i]
    sys.stdout.write( \
      '      <g transform="translate('+ dts(key_box_dx) + ','+ dts(key_ty) +')">\n' \
    )
    output_key_fun_block_item(op,tb,dim, tb.key_str[i], tb.key_sty[i], hsh_ty - key_ty)
    sys.stdout.write( \
      '      </g>\n' \
    )
    key_ty = key_ty + dim.box_wy + dim.key_col_sy
  ################################################################
  
def output_key_fun_block_item(op,tb,dim, kstr, ksty, hsh_box_dy) :
  "Writes one key box and its function arrow to {stdout}."
  "\n" \
  "  Expects the key string {kstr}, its style {ksty} ('N', 'C', etc.)" \
  " and the Y displacement {hsh_box_dy} between" \
  " the top of the key box and the top of the correspondng hash value box."

  # All positions computed here are relative to the upper left corner of the key box.

  # X positions of main points of of hash arrow:
  arr_B_x = dim.key_box_wx + dim.fun_col_sx/2   # Start of bent arrow
  arr_L_x = dim.key_box_wx + dim.fun_col_sx     # First bend.   
  arr_R_x = arr_L_x + dim.fun_box_wx # Second bend.  
  arr_T_x = arr_R_x + dim.hsh_col_sx # End of arrow.

  if op.funcbox :
    # Move the bends inwards:
    arr_L_x = arr_L_x + 5 # First bend.   
    arr_R_x = arr_R_x - 5 # Second bend.  
  
  # Y positions of left and right ends of of hash arrow:
  arr_L_y = dim.box_wy/2     
  arr_R_y = arr_L_y - dim.box_wy/2 + hsh_box_dy + dim.box_wy/2
  
  if ksty == 'C' :
    arr_color = '#aaaaaa'
  else :
    arr_color = '#000000'
  key_str_ax = dim.key_box_wx/2   # X position of key string anchor point rel to key box.
  sys.stdout.write( \
    '        <use xlink:href="#key_box_'+ ksty +'" />\n' \
    '        <text x="'+ dts(key_str_ax) +'" y="14" stroke-width="0px" stroke="none">'+ kstr +'</text>\n' \
    '        <line' \
               ' x1="'+ dts(arr_B_x) +'" y1="'+ dts(arr_L_y) +'"' \
               ' x2="'+ dts(arr_L_x) +'" y2="'+ dts(arr_L_y) +'"' \
               ' stroke="'+ arr_color +'"' \
               ' />\n' \
    '        <line' \
               ' x1="'+ dts(arr_L_x) +'" y1="'+ dts(arr_L_y) +'"' \
               ' x2="'+ dts(arr_R_x) +'" y2="'+ dts(arr_R_y) +'"' \
               ' stroke="'+ arr_color +'"' \
               ' />\n' \
    '        <line' \
               ' x1="'+ dts(arr_R_x) +'" y1="'+ dts(arr_R_y) +'"' \
               ' x2="'+ dts(arr_T_x) +'" y2="'+ dts(arr_R_y) +'"' \
               ' stroke="'+ arr_color +'"' \
               ' marker-end="url(#arrowtip_'+ ksty +')"' \
               ' />\n' \
  )
  ################################################################

def output_hsh_buc_block(op,tb,dim, ovf_dx) :
  "Writes the hash-value and bucket-array block to {stdout}."
  
  # All dimensions computed here are relative to the hash function block.

  # X positions of the hash and bucket boxes:
  hsh_box_dx = 0

  # baselines of the two header lines:
  tit_dy_top = - dim.tit_sy - dim.tit_wy
  tit_dy_bot = - dim.tit_sy

  if dim.buc_box_wx > 0 :
    tit_str = 'ячейки'
    tit_ax = hsh_box_dx + dim.hsh_box_wx + dim.buc_col_sx + dim.buc_box_wx/2 - 10
  else :
    tit_str = 'хэш-коды'
    tit_ax = hsh_box_dx + dim.hsh_box_wx/2
  # Title for column of hash values:
  sys.stdout.write( \
    '      <text x="'+ dts(tit_ax) +'" y="'+ dts(tit_dy_bot) +'" font-size="15px"' \
            ' font-weight="bold" fill="#000000" stroke-width="0px" stroke="none">\n' \
            ' '+ tit_str + '\n' \
            ' </text>\n' \
  )
  sys.stdout.write('\n')

  # Column of hash boxes and buckets:
  hsh_ty = dim.hsh_col_ty  # Y position of next hash box.
  for j in range(tb.nbucs) :
    sys.stdout.write( \
      '      <g transform="translate(000,'+ dts(hsh_ty) + ')">\n' \
    )
    # Compute Y displacement {ovf_dy} between top of bucket box and top of overflow box (if any):
    if tb.buc_oix[j] != -1 :
      ovf_ty = dim.ovf_col_ty + tb.buc_oix[j]*(dim.box_wy + dim.ovf_col_sy) # Top of overflow box.
      ovf_dy = ovf_ty - hsh_ty
    else :
      ovf_dy = None
    if tb.buc_hsh[j] < 0 :
      hsh_str = ':'
    else :
      hsh_str = ("%0*d" % (dim.hsh_ndg, tb.buc_hsh[j]))
    output_hsh_buc_block_item(op,tb,dim, hsh_str, tb.buc_hsh_sty[j], tb.buc_kix[j], tb.buc_oix[j], ovf_dx, ovf_dy)
    sys.stdout.write( \
      '      </g>\n' \
    )
    hsh_ty = hsh_ty + dim.box_wy
  ################################################################

def output_hsh_buc_block_item(op,tb,dim, hstr, hsty, kix, oix, ovf_dx, ovf_dy) :
  "Writes one hash value box, its bucket box, and the pointer (if any) to {stdout}."
  "\n" \
  "  Expects the formatted hash value string {hstr}, its style {hsty} ('N', 'C', 'U', or ':')" \
  " and the Y displacement {ovf_dy} between the top of the bucket box and" \
  " the top of the pointed entry box.  Also gets the index {kix} of" \
  " the key which is stored into the bucket, or -1 if the bucket" \
  " is vacant or a vdots. This index is used to obtain the" \
  " entry's key and/or value.\n" \
  "\n" \
  "  Also requires index {oix} of the overflow entry that the bucket points to, or -1 if" \
  " not applicable.  If {oix} is not -1, also expects the displacements {ovf_dx,ovf_dy} from" \
  " the top left corner of the hash box to the top left corner of that overflow box."
  box_dx = 0;

  # Hash value box:
  box_wx = dim.hsh_box_wx;
  output_box(op,tb,dim, box_dx, 'hsh_box', hsty, box_wx, hstr)
  box_dx = box_dx + box_wx

  # Choose the style for the bucket box and null pointers in it:
  if hsty == ':' :
    bsty = ':'
    psty = ':'
  elif kix == -1 :
    bsty = 'U'
    psty = 'U' 
  else :
    bsty = 'E'
    psty = 'N'

  if tb.buc_has_key :
    # Stored key box:
    box_wx = dim.key_box_wx;
    if kix == -1 : bstr = ''
    else : bstr = tb.key_str[kix]
    output_box(op,tb,dim, box_dx, 'key_box', bsty, box_wx, bstr)
    box_dx = box_dx + box_wx

  if tb.buc_has_val :
    # Stored value box:
    box_wx = dim.val_box_wx;
    if kix == -1 : bstr = ''
    else : bstr = tb.val_str[kix]
    output_box(op,tb,dim, box_dx, 'val_box', bsty, box_wx, bstr)
    box_dx = box_dx + box_wx

  if tb.buc_has_ptr :
    # Pointer box in bucket:
    box_wx = dim.ptr_box_wx;
    output_box(op,tb,dim, box_dx, 'ptr_box', bsty, box_wx, '')
    if bsty != ':' :
      output_buc_ovf_arrow(op,tb,dim, box_dx, box_wx, psty, oix, ovf_dx, ovf_dy)
    box_dx = box_dx + box_wx
  ################################################################

def output_buc_ovf_arrow(op,tb,dim, box_dx, box_wx, psty, oix, ovf_dx, ovf_dy) :
  "Writes an arrow from a bucket pointer to an overflow entry {stdout}.\n" \
  "\n" \
  "  Requires the X position and width of the link box, and the index {oix}" \
  " of the overflow entry that the bucket points to.  If {oix} is -1, assumes" \
  " that the link is null, and draws a marker \"linkdot_{psty}\" where {psty} should" \
  " be either \"N\" or \"U\".  If {oix} is not -1, also" \
  " expects the displacements {ovf_dx,ovf_dy} from the top left corner of the hash box" \
  " to the top left corner of that overflow box; in that case {psty} had better be \"N\"."

  # All positions computed here are relative to the upper left corner of the key box.

  # X positions of main points of of hash arrow:
  arr_B_x = box_dx + box_wx/2  # Start X of arrow
  arr_B_y = dim.box_wy/2       # Start Y of arrow
  if oix < 0 :
    # Null pointer - use a very short arrow with base but not tip:
    arr_T_x = arr_B_x + 0.001 # End X of arrow.
    arr_T_y = arr_B_y         # End Y of arrow.
  else :
    # Non-null pointer: point to the mille of the left side of the target box:
    arr_T_x = ovf_dx                 # End X of arrow.
    arr_T_y = ovf_dy + dim.box_wy/2  # End Y of arrow.

  sys.stdout.write( \
    '        <line' \
               ' x1="'+ dts(arr_B_x) +'" y1="'+ dts(arr_B_y) +'"' \
               ' x2="'+ dts(arr_T_x) +'" y2="'+ dts(arr_T_y) +'"' \
               ' stroke="#000000"' \
               ' marker-start="url(#linkdot_'+ psty + ')"' \
  )
  if oix >= 0 :
    sys.stdout.write( \
               ' marker-end="url(#arrowtip_N)"' \
    )
  sys.stdout.write( \
               ' />\n' \
  )
  
  ################################################################

def output_ovf_block(op,tb,dim) :
  "Writes the overflow entries block to {stdout}."
  
  # All dimensions computed here are relative to the overflow entries block.

  # X positions of the overflow boxes:
  ovf_box_dx = 0

  # Baselines and alignment of the two header lines:
  tit_dy_top = - dim.tit_sy - dim.tit_wy
  tit_dy_bot = - dim.tit_sy
  tit_ax = dim.ovf_box_wx/2 + 10
  
  # Title for column of overflow entries:
  if op.links == 0 :
    sys.stdout.write( \
      '      <text x="'+ dts(tit_ax) +'" y="'+ dts(tit_dy_top) +'" font-size="15px"' \
              ' font-weight="bold" fill="#000000" stroke-width="0px" stroke="none">\n' \
              ' overflow\n' \
              ' </text>\n' \
    )
  sys.stdout.write( \
    '      <text x="'+ dts(tit_ax) +'" y="'+ dts(tit_dy_bot) +'" font-size="15px"' \
            ' font-weight="bold" fill="#000000" stroke-width="0px" stroke="none">\n' \
            ' состояния\n' \
            ' </text>\n' \
  )
  sys.stdout.write('\n')

  # Column of overflow entries:
  ovf_ty = dim.ovf_col_ty  # Y position of next overflow entry.
  for j in range(tb.novfs) :
    sys.stdout.write( \
      '      <g transform="translate(000,'+ dts(ovf_ty) + ')">\n' \
    )
    output_ovf_block_item(op,tb,dim, tb.ovf_kix[j], tb.ovf_pix[j])
    sys.stdout.write( \
      '      </g>\n' \
    )
    ovf_ty = ovf_ty + dim.box_wy + dim.ovf_col_sy
  ################################################################

def output_ovf_block_item(op,tb,dim, kix, pix) :
  "Writes one overflow entry box and its pointer (if any) to {stdout}."
  "\n" \
  "  Expects the index {kix} of the key to which the entry belongs.  Also expects"
  " the index {pix} of the next block in the chain, or -1 if none."
  box_dx = 0;

  assert (kix != -1)

  # Overfow entries are never vacant or ':':
  bsty = 'E'

  if tb.ovf_has_ptr :
    # Entry pointer box:
    box_wx = dim.ptr_box_wx;
    output_box(op,tb,dim, box_dx, 'ptr_box', bsty, box_wx, '')
    ptr_dy = dim.box_wy + dim.ovf_col_sy
    output_ovf_ptr_arrow(op,tb,dim, box_dx, box_wx, pix, ptr_dy)
    box_dx = box_dx + box_wx
  
  if tb.ovf_has_key :
    # Stored key box:
    box_wx = dim.key_box_wx;
    bstr = tb.key_str[kix]
    output_box(op,tb,dim, box_dx, 'key_box', bsty, box_wx, bstr)
    box_dx = box_dx + box_wx

  if tb.ovf_has_val :
    # Stored value box:
    box_wx = dim.val_box_wx;
    bstr = tb.val_str[kix]
    output_box(op,tb,dim, box_dx, 'val_box', bsty, box_wx, bstr)
    box_dx = box_dx + box_wx
  ################################################################

def output_ovf_ptr_arrow(op,tb,dim, box_dx, box_wx, pix, ptr_dy) :
  "Writes an arrow from an overflow entry to the entry below it {stdout}.\n" \
  "\n" \
  "  Requires the X position and width of the link box, and the index {pix}" \
  " of the next overflow entry.  If {pix} is -1, assumes that the link is null, and" \
  " draws some appropriate symbol.  If {pix} is not -1, also expects the" \
  " Y displacement {ptr_dy} from the top left corner of the link box" \
  " to the top left corner of the link box of the linked-to entry.\n" \
  "\n" \
  "  At present, uses a straight arrow, so the two entries must be" \
  " consecutive in the overflow column."

  # All positions computed here are relative to the upper left corner of the key box.

  # X positions of main points of of hash arrow:
  arr_B_x = box_dx + box_wx/2  # Start X of arrow
  arr_B_y = dim.box_wy/2       # Start Y of arrow
  if pix < 0 :
    # Null pointer - use a very short arrow with base but not tip:
    arr_T_x = arr_B_x          # End X of arrow.
    arr_T_y = arr_B_y + 0.001  # End Y of arrow.
  else :
    # Non-null pointer: point to the mille of the left side of the target box:
    arr_T_x = arr_B_x  # End X of arrow.
    arr_T_y = ptr_dy   # End Y of arrow.

  sys.stdout.write( \
    '        <line' \
               ' x1="'+ dts(arr_B_x) +'" y1="'+ dts(arr_B_y) +'"' \
               ' x2="'+ dts(arr_T_x) +'" y2="'+ dts(arr_T_y) +'"' \
               ' stroke="#000000"' \
  )
  if pix < 0 :
    sys.stdout.write( \
               ' marker-start="url(#linkdot_U)"' \
    )
  else :
    sys.stdout.write( \
               ' marker-start="url(#linkdot_N)"' \
               ' marker-end="url(#arrowtip_N)"' \
    )
  sys.stdout.write( \
               ' />\n' \
  )

  ################################################################

def output_box(op,tb,dim, box_dx, btyp, bsty, box_wx, str) :
  "Outputs a single box of an entry in the bucket array or overflow area.\n" \
  "\n" \
  "  Takes the box X position {box_dx}, the box type {btyp}" \
  " (\'key_box\', \'hsh_box\', etc.), the box style" \
  " {bsty} (\'N\', \'C\',etc.),the box width {box_wx}, and" \
  " the string to display inside the box.  If {bsty} is \':\', omits" \
  " the box and shows only the \':\' in bold type."
  
  str_ax = box_dx + box_wx/2   # X position of key string anchor point rel to key box.
  if bsty == ':' :
    sys.stdout.write( \
      '        <text x="'+ dts(str_ax) +'" y="14" font-weight="bold">:</text>\n' \
    )
  else:
    sys.stdout.write( \
      '        <use x="'+ dts(box_dx) +'" xlink:href="#'+ btyp + '_'+ bsty + '" />\n' \
    )
    if (str != ':') and (str != '') :
      sys.stdout.write( \
        '        <text x="'+ dts(str_ax) +'" y="14">' + str +'</text>\n' \
      )
  ################################################################

def output_figure_postamble(op,tb,dim) :
  "Writes the SVG postamble to {stdout}."

  sys.stdout.write( \
    '  </g>\n' \
    '</svg>\n' \
  )
################################################################

# Main program:
op = parse_args()
output_figure(op)
