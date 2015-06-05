type entry = Entry of int
type page_id = Page_id of int
type key = Key of int

let maxN = 4

type inode = I of (key list * page_id list)
type lnode = L of (entry list)
type node = INode of inode | LNode of lnode


module Page_id_order (* : Map.OrderedType with type t = page_id *) = struct

  type t = page_id

  let compare = (Pervasives.compare: t-> t -> int)

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

let get_m s0 r = (
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
  if i=j then [i] else i::(from_to (i+1) j)
)

let _ = from_to 1 5

let wf_btree s0 (r,ss0,n0) h = (match h with
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
        let h = h_plus_one -1 in
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
                        let pred i = 
                          let (qi,si,mi) = (qq i, ss i, mm i) in
                          wf_btree s0 (qi,si,mi) h
                        in
                        match List.for_all pred (from_to 1 n) with
                        | false -> false
                        | true -> (
                            (* check S = S_1 Un ... *)
                            let union = (from_to 1 n) |> List.map ss |> union_list_of_entry_set in
                            match Entry_set.equals ss0 union with
                            | false -> false
                            | true -> (
                                let cond_sj = (
                                  let js = from_to 1 (n-1) in
                                  let f3 j = 
                                    let sj = ss j in
                                    let dj = dd j in
                                    let dj' = dd (j+1) in
                                    Entry_set.for_all (fun s -> s |> entry_to_key |> (fun k -> dj <= k)) sj  (* NB use of ocaml <= for type key *)
                                    && Entry_set.for_all (fun s -> s |> entry_to_key |> (fun k -> k < dj')) sj
                                  in
                                  List.for_all f3 js
                                )
                                in
                                match cond_sj with
                                | false -> false
                                | true -> (
                                    let cond_mj = (
                                      let js = from_to 1 n in
                                      let max_2 = (maxN+1) / 2 in (* FIXME check *)
                                      let pred j = 
                                        max_2 <= mm j
                                      in
                                      List.for_all pred js
                                    )
                                    in
                                    match cond_mj with
                                    | false -> false
                                    | true -> (
                                        let d1 = dd 1 in
                                        let s1 = ss 1 in
                                        let cond_s1 = Entry_set.for_all (fun s -> s |> entry_to_key |> (fun k -> k < d1)) s1 in
                                        match cond_s1 with
                                        | false -> false
                                        | true -> (
                                            let dn' = dd (n-1) in
                                            let sn = ss n in
                                            let cond_sn = Entry_set.for_all (fun s -> s |> entry_to_key |> (fun k -> dn' <= k)) sn in
                                            cond_sn
                                          )
                                      )
                                      
                                  )
                              )

                          )                    
                      )
                          

                  )
              )
          )
      )
  )


let _ = wf_btree empty_store0 (root0,Entry_set.empty,0) 1
