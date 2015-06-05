(*
let trans c0 = (
  match c0 with

  | (Insert(a),r,pi,sg) when (
    match(store_map_find sg r) with
    | Some(INode(I(ds,ps))) -> true
    | _ -> false) -> (
      match (store_map_find sg r) with
      | Some(INode(I(ds,ps))) -> (
          let i = first ds (fun x -> x > entry_to_key(a)) in
          (Insert(a),nth_from_1 ps i,(r,i)::pi,sg)
        )
      | _ -> failwith "impossible svb"      
    )

  | (Insert(a),r,pi,sg) when (
    match (store_map_find sg r) with
    | Some(LNode(L(es))) -> (
        let i = first es (fun x -> entry_to_key x >= entry_to_key a) in
        test i es (fun x -> entry_to_key x = entry_to_key a)
      ) 
    | _ -> false) -> (
      match (store_map_find sg r) with
      | Some(LNode(L(es))) -> (
          let i = first es (fun x -> entry_to_key x >= entry_to_key a) in
          let l' = LNode(L(replace(a,i,es))) in
          (S,r,pi,Store_map.add r l' sg)
        )
      | _ -> failwith "impossible 8ja"
    )

)
*)
