type entry = Entry of int
type page_id = Page_id of int
type key = Key of int

let maxN = 4

type inode = I of (key list * page_id list)
type lnode = L of (entry list)
type node = INode of inode | LNode of lnode


module Page_id_order (* : Map.OrderedType with type t = page_id *) = struct

  type t = page_id

  let compare = (Pervasives.compare: t -> t -> int)

end

module Store_map = Map.Make(Page_id_order)

type store = node Store_map.t

(* initial root pointer *)
let root0 = Page_id(0)

let empty_store0 = Store_map.empty |> Store_map.add root0 (LNode(L[]))

let _ = Store_map.bindings empty_store0


module Entry_order = struct

  type t = entry
  let compare = (Pervasives.compare: t-> t -> int)

end

module Entry_set = Set.Make(Entry_order)

let store_map_find s0 k = (
  try 
    Some(Store_map.find k s0)
  with _ -> None)

(* called key in paper *)
let entry_to_key e = (match e with
    | Entry(i) -> Key(i))

let entry_lt e1 e2 = ( (entry_to_key e1) < (entry_to_key e2) )

(* sorted in strictly ascending order *)
let sorted_entry_list es = (
  let entry_compare e1 e2 = (
    if e1=e2 then 0 else 
    if entry_lt e1 e2 then -1 else
    1)
  in
  (List.sort entry_compare es) = es)

let _ = sorted_entry_list [Entry(1);Entry(2);Entry(3)]
let _ = sorted_entry_list [Entry(1);Entry(2);Entry(3);Entry(2)]


let union_list_of_entry_set xs = 
  let f1 acc sofar = Entry_set.union acc sofar in
  xs |> (fun xs -> List.fold_left f1 Entry_set.empty xs)

let rec entry_set s0 r = (
  match store_map_find s0 r with
  | None -> Entry_set.empty
  | Some(node) -> (
      match node with
      | LNode(L(es)) -> Entry_set.of_list(es)
      | INode(I(ds,qs)) -> (
          let union_of_sets_for_subtrees = qs |> List.map (entry_set s0) |> union_list_of_entry_set in
          union_of_sets_for_subtrees
        )
    )
)

let tmp = empty_store0 |> Store_map.add root0 (LNode(L([Entry(1)])))

let _ = (entry_set empty_store0 root0) |> Entry_set.elements
let _ = (entry_set tmp root0) |> Entry_set.elements

let get_m: node Store_map.t -> Store_map.key -> int option = (fun s0 r ->
  match store_map_find s0 r with
  | None -> None
  | Some(node) -> (
      match node with
      | LNode(L(es)) -> (Some(List.length es))
      | INode(I(ds,qs)) -> (Some(List.length qs))
    )
)

(* nth_from_1 xs 1 is the first elt of xs - we count from 1 not 0 *)
let nth_from_1 xs i = List.nth xs (i-1)

(* a list containing i..j; hacky *)
let rec from_to i j = (
  if i=j then [i]
  else
    if i<j
    then i::(from_to (i+1) j)
    else []
)

let _ = from_to 1 0
let _ = from_to 1 5

let rec wf_btree s0 (r,ss0,n0) h = (match h with
    | 0 -> false
    | 1 -> (
        match store_map_find s0 r with
        | None -> false
        | Some(node) -> (
            match node with
            | INode _ -> false
            | LNode (L(es)) -> (
                let n = List.length es in
                match (n=n0) && n <= maxN with
                | false -> false
                | true -> (
                    (* construct a set of entries from es *)
                    let ss' = Entry_set.of_list(es) in
                    match Entry_set.equal ss0 ss' with
                    | false -> false
                    | true -> (
                        sorted_entry_list es )
                  )
              )
          )
      )
    | h_plus_one -> (
        let h = h_plus_one - 1 in
        match store_map_find s0 r with
        | None -> false
        | Some(node) -> (
            match node with
            | LNode _ -> false
            | INode(I(ds,qs)) -> (
                match (n0 = List.length qs) && (List.length ds + 1 = List.length qs) with 
                | false -> false
                | true -> (
                    (* do we know length n0 ~= 0 or 1? n0 cannot be 0, because it is 1 bigger than |ds| *)
                    (* "minimum occupancy of each child node to be at
                       least half its maximum capacity (maxN)" - FIXME is
                       this true if n=1? *)
                    (* the predicate mentions d1, which means that ds can't be []; this implies that n >= 2 *)
                    (* FIXME but for btrees don't we need some
                       properties of the number of keys in each node in
                       relation to maxN? *)
                    match ds with
                    | [] -> false
                    | d1::_ -> (
                        let n = n0 in
                        let _ = assert (n >= 2) in
                        let qq i = nth_from_1 qs i in
                        let ss i = i |> qq |> (entry_set s0) in
                        let mm i = i |> qq |> (get_m s0) in
                        let dd i = nth_from_1 ds i in
                        let rec_clause =
                          let pred i =
                            let (qi,si,mi) = (qq i, ss i, mm i) in
                            match mi with
                            | None -> false
                            | Some(mi) -> (wf_btree s0 (qi,si,mi) h)
                          in
                          List.for_all pred (from_to 1 n)
                        in
                        let union_clause =
                          (* check S = S_1 Un ... *)
                          let union = (from_to 1 n) |> List.map ss |> union_list_of_entry_set in
                          Entry_set.equal ss0 union
                        in
                        let cond_sj = (
                          let js = from_to 1 (n-2) in
                          let f3 j =
                            let sj' = ss (j+1) in
                            let dj  = dd j     in
                            let dj' = dd (j+1) in
                            Entry_set.for_all (fun s -> s |> entry_to_key |> (fun k -> dj <= k)) sj'  (* NB use of ocaml <= for type key *)
                            && Entry_set.for_all (fun s -> s |> entry_to_key |> (fun k -> k < dj')) sj'
                          in
                          List.for_all f3 js
                        )
                        in
                        let cond_mj = (
                          let js = from_to 1 n in
                          let max_2 = (maxN+1) / 2 in (* FIXME check *)
                          let pred j =
                            match mm j with
                            | None -> false
                            | Some(mj) -> max_2 <= mj
                          in
                          List.for_all pred js
                        )
                        in
                        let cond_s1 = (
                          let d1 = dd 1 in
                          let s1 = ss 1 in
                          Entry_set.for_all (fun s -> s |> entry_to_key |> (fun k -> k < d1)) s1)
                        in
                        let cond_sn = (
                          let dn' = dd (n-1) in
                          let sn = ss n in
                          Entry_set.for_all (fun s -> s |> entry_to_key |> (fun k -> dn' <= k)) sn)
                        in
                        rec_clause && union_clause && cond_sj && cond_mj && cond_s1 && cond_sn
                      )
                  )
              )
          )
      )
  )


let _ = wf_btree empty_store0 (root0,Entry_set.empty,0) 1


(* section 3: insertion as abstract machine rules *)

type ins_comm = Insert of entry | S | D of (key * page_id) | Ret

type config = ins_comm * page_id * ((page_id * int)list) * store

let initial_config a (r,s) = (Insert(a),r,[],s)

let first xs p = (
  let rec f1 i =
    if i <= List.length xs then
      if p (nth_from_1 xs i) then i else f1 (i+1)
    else
      List.length xs + 1
  in
  f1 1)

let _ = first [1;2;3] (fun x -> x=5)

let test k xs p = (
  if (1 <= k && k <= List.length xs) then
    p (nth_from_1 xs k)
  else
    false)

let rec replace(a,i,es) = (
  match i with
  | 0 -> failwith "replace: 0"
  | 1 -> (
      match es with
      | [] -> failwith "replace: es=[]"
      | x::xs -> a::xs)
  | _ -> (
      match es with
      | [] -> failwith "replace: es=[] 2"
      | e::es -> e::replace(a,i-1,es)))

let rec ins (a,i,xs) = (
  match i with
  | 0 -> failwith "ins: 0"
  | 1 -> a::xs
  | _ -> (
      match xs with
      | [] -> failwith "ins: []"
      | x::xs -> x::(ins (a,i-1,xs))))

let rec take2 xs n = (
  match n with
  | 0 -> ([],xs)
  | _ -> (
      match xs with
      | [] -> ([],[])
      | x::xs -> (
          let (b,c) = (take2 xs (n-1)) in
          ((x::b),c))))


let split_l (i,a,es0) = (
  let es = ins(a,i,es0) in
  let (es',es'') = take2 es (List.length es / 2) in
  let k = (
    match es'' with
    | [] -> failwith "impossible split_l"
    | e::_ -> entry_to_key e)
  in
  (es',k,es''))

let free_page_id s0 = (
  let rec f1 x = (
    if Store_map.mem (Page_id x) s0 then f1 (x+1) else Page_id(x)
  )
  in
  f1 0)

(*
let trans' c0 = (
  match c0 with
  | (c,r,pi,sg) -> (
      match c with
      | Insert(a) -> (
          match (store_map_find sg r) with
          | Some(INode(I(ds,ps))) -> (
              let i = first ds (fun x -> x > entry_to_key(a)) in
              Some(Insert(a),nth_from_1 ps i,(r,i)::pi,sg)
            )
          | Some(LNode(L(es))) -> (
              let i = first es (fun x -> entry_to_key x >= entry_to_key a) in
              if test i es (fun x -> entry_to_key x = entry_to_key a) then
                let l' = LNode(L(replace(a,i,es))) in
                Some(S,r,pi,Store_map.add r l' sg)
              else if List.length es < maxN then
                let l' = LNode(L(ins(a,i,es))) in
                Some(S,r,pi,Store_map.add r l' sg)
              else
                let (es',k,es'') = split_l(i,a,es) in
                let l1 = LNode(L(es')) in
                let l2 = LNode(L(es'')) in
                let q = free_page_id sg in
                let sg' = sg |> Store_map.add r l1 |> Store_map.add q l2 in
                Some(D(k,q),r,pi,sg')
            )
      )
      | x -> None
    )
)


NOTE: reduced the match case because we can better respect the phases of the paper *)

let split_i (i,k,q,d,p) = (
  let _ = assert (List.length p = ((List.length d)+1)) in
  let (d',k'::d'') =
    let ds = ins(k,i,d) in
    take2 ds ((List.length ds)/2) in
  let (p',p'') =
    let ps = ins(q,i+1,p) in
    take2 ps ((List.length d')+1)
  in
  let _ = assert (List.length p' = ((List.length d')+1)) in
  let _ = assert (List.length p'' = ((List.length d'')+1)) in
  let _ = assert ((List.length p') - (List.length p'') <=1) in
  (d',p',k',d'',p'')
)

let insert_trans c0 = (
  match c0 with
  | (Insert(a),r,pi,sg) -> (
    match (store_map_find sg r) with
    | Some(INode(I(ds,ps))) -> (
      let i = first ds (fun x -> x > entry_to_key(a)) in
      Some(Insert(a),nth_from_1 ps i,(r,i)::pi,sg)
    )
    | Some(LNode(L(es))) -> (
      let i = first es (fun x -> entry_to_key x >= entry_to_key a) in
      if test i es (fun x -> entry_to_key x = entry_to_key a) then
        let l' = LNode(L(replace(a,i,es))) in
        Some(S,r,pi,Store_map.add r l' sg)
      else if List.length es < maxN then
        let l' = LNode(L(ins(a,i,es))) in
        Some(S,r,pi,Store_map.add r l' sg)
      else
        let (es',k,es'') = split_l(i,a,es) in
        let l1 = LNode(L(es')) in
        let l2 = LNode(L(es'')) in
        let q = free_page_id sg in
        let sg' = sg |> Store_map.add r l1 |> Store_map.add q l2 in
        Some(D(k,q),r,pi,sg')
    )
    | None -> failwith "impossible: at least root in"
  )
  | (S,r,((t,i)::pi),sg) -> Some (S,t,pi,sg) (* if we did not need to split the tree, we just clean the list of added entries *)
  | (D(k,q),r,(t,i)::pi,sg) ->
     let (I(d,p)) =
       match store_map_find sg t with
       | Some INode inode-> inode
       | _ -> failwith "impossible: D"
     in
     (match ((List.length p) < maxN) with
     | true ->
        let i' = INode(I(ins(k,i,d),ins(q,i+1,p))) in
        let sg' = sg |> Store_map.add t i' in
        Some (S,t,pi,sg')
     | false ->
        let (d',p',k',d'',p'') = split_i(i,k,q,d,p) in
        let i' = INode(I(d',p'))   in
        let i''= INode(I(d'',p'')) in
        let q' = free_page_id sg in
        let sg' = sg |> Store_map.add t i' |> Store_map.add q' i'' in
        Some (D(k',q'),t,pi,sg'))
  | (S,r,[],sg) -> Some (Ret,r,[],sg)
  | (D(k,t),r,[],sg) ->
     let q = free_page_id sg in
     let sg' = sg |> Store_map.add q (INode(I([k],[r;t]))) in
     Some(Ret,q,[],sg')
  | _ -> None
)


let rec insert_loop c0 = (
  match insert_trans c0 with
  | None -> c0
  | Some c -> insert_loop c)

let config0 = (Insert(Entry(2)),root0,[],empty_store0)

let (a,b,c,d) = insert_loop config0
let _ = Store_map.bindings d


let inserts_in_tree (r0,s0) l =
  let dest_root_store (_,r,_,s) = (r,s) in
  List.fold_left (fun (r,s) e ->  dest_root_store(insert_loop (Insert(Entry(e)),r,[],s))) (r0,s0) l

(* tests *)
let get_set_entries sg =
  Entry_set.of_list (
      List.fold_left
        (fun acc (_,n) -> match n with | LNode(L(es)) -> acc @ es | _ -> acc)
        []
        (Store_map.bindings sg))

let (root,store_with_full_root) = inserts_in_tree (root0,empty_store0) [1;2;3;4;5]
let _ = Store_map.bindings store_with_full_root

let _ = wf_btree store_with_full_root (root,(get_set_entries store_with_full_root),4) 1

let (root',store_with_two_children) = inserts_in_tree (root,store_with_full_root) [5;6]
let _ = Store_map.bindings store_with_two_children

let _ = wf_btree store_with_two_children (root',(get_set_entries store_with_two_children),2) 2

let (root'',store_with_two_inodes) = inserts_in_tree (root',store_with_two_children) [7;8;9]
let _ = Store_map.bindings store_with_two_inodes

let _ = wf_btree store_with_two_inodes (root'',(get_set_entries store_with_two_inodes),4) 2

let (root''',store_with_three_inodes) = inserts_in_tree (root'',store_with_two_inodes) [10;11;12;13;14;15;16]
let _ = Store_map.bindings store_with_three_inodes

let _ = wf_btree store_with_three_inodes (root''',(get_set_entries store_with_three_inodes),2) 3

(* end tests *)

type find_comm = Find of key | Ret of (page_id * int)

type find_config = find_comm * page_id * store

let find_trans (Find(k),r,sg) =
  (match (store_map_find sg r) with
   | Some (INode(I(ds,ps))) ->
      let i = first ds (fun x -> x > k) in
      let p = nth_from_1 ps i in
      (Find(k),p,sg)
   | Some (LNode(L(es))) ->
      let i = first es (fun x -> (entry_to_key x) >= k) in
      (Ret(r,i),r,sg)
   | None -> failwith "find: invalid root")

let rec find_loop c0 = (
  match find_trans c0 with
  | (Ret (r,i), _, sg) ->
     (match (store_map_find sg r) with
     | None -> None
     | Some(LNode(L(qs))) -> try Some(nth_from_1 qs i) with _ -> None
     | _ -> failwith "impossible: inode should not be returned")
  | c -> find_loop c)

let find_config0 = Find(Key 52), root'' , store_with_two_inodes
let entry  = find_loop find_config0
