(*

This lines are to record instructions for interactive use.

Interactive before anything else:

    #use "topfind";;
    #require "num";;
    #require "zarith";;
    #directory "../../src_ext/lem/ocaml-lib/";;
    #load "extract.cma";;
    #directory "gen_ocaml/";;
    #mod_use "btree.ml";;
 *)


open Btree
(* open Utility *)
(* open Fs_impl_types *)
(* open BTree *)

let bindings store = Pmap.fold (fun k d a -> (k,d)::a ) store []

let (r,s) = (BTree.inserts_in_tree Fs_impl_types.nat_env (Fs_impl_types.Page_id( 0),Fs_impl_types.nat_empty_btree_store) [Fs_impl_types.Entry( 1);Fs_impl_types.Entry( 2);Fs_impl_types.Entry( 3);Fs_impl_types.Entry( 4);Fs_impl_types.Entry( 5)])
let _ = bindings s

let (r',s') = (BTree.inserts_in_tree Fs_impl_types.nat_env (r,s) [Fs_impl_types.Entry( 6);Fs_impl_types.Entry( 7);Fs_impl_types.Entry( 8);Fs_impl_types.Entry( 9);Fs_impl_types.Entry( 10);Fs_impl_types.Entry( 11)])
let _ = bindings s'

let (i,s') = BTree.find_h Fs_impl_types.nat_env (Some(Fs_impl_types.Find(Fs_impl_types.Key 10)), r',s') 3
let _ = bindings s'

let _ = BTree.find_h Fs_impl_types.nat_env (Some(Fs_impl_types.Find(Fs_impl_types.Key 10)), Fs_impl_types.Page_id( 0) ,Fs_impl_types.nat_empty_btree_store) 3


let (d_i,d_s) = BTree.delete_entries Fs_impl_types.nat_env (r,s) [Fs_impl_types.Entry 4]
let _ = bindings d_s

(* steal_right *)
let (d_i,d_s) = BTree.delete_entries Fs_impl_types.nat_env (r,s) [Fs_impl_types.Entry 2]
let _ = bindings d_s

(* merge_right *)
let (d_i',d_s') = BTree.delete_entries Fs_impl_types.nat_env (d_i,d_s) [Fs_impl_types.Entry 4]
let _ = bindings d_s'

(* merge_left *)
let (d_i',d_s') = BTree.delete_entries Fs_impl_types.nat_env (d_i,d_s) [Fs_impl_types.Entry 1]
let _ = bindings d_s'


(* steal left of inodes *)
let (bt_r,bt_s) = (BTree.inserts_in_tree Fs_impl_types.nat_env (r,s) [Fs_impl_types.Entry( 1);Fs_impl_types.Entry( 2);Fs_impl_types.Entry( 3);Fs_impl_types.Entry( 4);Fs_impl_types.Entry( 5); Fs_impl_types.Entry( 6);Fs_impl_types.Entry( 7);Fs_impl_types.Entry( 8);Fs_impl_types.Entry( 9);Fs_impl_types.Entry( 10);Fs_impl_types.Entry( 11)])
let _ = bindings bt_s


let (d_i',d_s') = BTree.delete_entries Fs_impl_types.nat_env (bt_r,bt_s) [Fs_impl_types.Entry 7;Fs_impl_types.Entry 8]
let _ = bindings d_s'

(* steal right inode *)
let (bt_r,bt_s) = (BTree.inserts_in_tree Fs_impl_types.nat_env (r,s) [Fs_impl_types.Entry( 1);Fs_impl_types.Entry( 2);Fs_impl_types.Entry( 3);Fs_impl_types.Entry( 4);Fs_impl_types.Entry( 5); Fs_impl_types.Entry( 6);Fs_impl_types.Entry( 7);Fs_impl_types.Entry( 8);Fs_impl_types.Entry( 9);Fs_impl_types.Entry( 10);Fs_impl_types.Entry( 11);Fs_impl_types.Entry( 12);Fs_impl_types.Entry( 13);])
let _ = bindings bt_s
let (d_i',d_s') = BTree.delete_entries Fs_impl_types.nat_env (bt_r,bt_s) [Fs_impl_types.Entry 5;Fs_impl_types.Entry 6;Fs_impl_types.Entry 4]
let _ = bindings d_s'


(* merge right inodes *)
let (bt_r,bt_s) = (BTree.inserts_in_tree Fs_impl_types.nat_env (r,s) [Fs_impl_types.Entry( 1);Fs_impl_types.Entry( 2);Fs_impl_types.Entry( 3);Fs_impl_types.Entry( 4);Fs_impl_types.Entry( 5); Fs_impl_types.Entry( 6);Fs_impl_types.Entry( 7);Fs_impl_types.Entry( 8);Fs_impl_types.Entry( 9);Fs_impl_types.Entry( 10);Fs_impl_types.Entry( 11);Fs_impl_types.Entry( 12);Fs_impl_types.Entry( 13);Fs_impl_types.Entry( 14);Fs_impl_types.Entry( 15);Fs_impl_types.Entry( 16);Fs_impl_types.Entry( 17)])
let _ = bindings bt_s
let (d_i',d_s') = BTree.delete_entries Fs_impl_types.nat_env (bt_r,bt_s) [Fs_impl_types.Entry 7;Fs_impl_types.Entry 87;Fs_impl_types.Entry 4;Fs_impl_types.Entry 1;Fs_impl_types.Entry 2]
let _ = bindings d_s'
