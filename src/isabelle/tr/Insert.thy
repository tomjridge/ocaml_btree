theory Insert
imports Common
begin

section types

datatype ('r) stk = Stk "('r page_ref * nat) list"

section "parameters"

section "insert,  ins_state, ins_step"

record ('bs,'k,'r,'v) ins_state_down = 
  isd_k :: "'k key"
  isd_v :: "'v value_t"
  isd_r :: "'r page_ref"
  isd_stk :: "'r stk"
  isd_str :: "('r,'bs) store"

record ('r) ins_state_up_1 = 
  isu1_r :: "'r page_ref"
  
(* r1 <= k < r2 *)
record ('k,'r,'v) ins_state_up_2 = 
  isu2_r1 :: "'r page_ref"
  isu2_k :: "'k key"
  isu2_r2 :: "'r page_ref"

datatype ('k,'r,'v) ins_state_up' = 
  S "'r ins_state_up_1"  (* inserting a single pointer *)
  | D "('k,'r,'v) ins_state_up_2"  (* inserting two pointers, separated by a key *)

record ('bs,'k,'r,'v) ins_state_up =
  isu_s :: "('k,'r,'v) ins_state_up'"
  isu_stk :: "'r stk"
  isu_str :: "('bs,'r) store"

datatype ('bs,'k,'r,'v) ins_state = 
  Down "('bs,'k,'r,'v) ins_state_down"
  | Up "('bs,'k,'r,'v) ins_state_up"


definition ins_step :: "('bs,'k,'r,'v) ctxt_k2r_t
  => ('bs,'k,'r,'v) ins_state 
  =>  ('bs,'k,'r,'v) ins_state option" where
  "ins_step ctxt1 s0 == (
case s0 of
    Down isd => (
      let r0 = isd|>isd_r in
      let frm = (page_ref_to_frame (ctxt_p2f_t.truncate ctxt1) (isd|>isd_str) r0) in
      case frm of
      None => None
      | Some frm0 => (
        case frm0 of
        Frm_I nf => (  
          let k2r = ((ctxt1|>key_to_ref)|>dest_key_to_ref) in
          let r' = k2r nf k0 in (* we need the index *)
          
        )
        | Frm_L lf => None
      )
    )
    | _ => arb
    
  )"



end


