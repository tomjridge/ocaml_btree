theory "PreludeLemmas" 

imports 
 	 Main "~~/src/HOL/Library/Code_Target_Numeral"
	 "../../src_ext/lem/isabelle-lib/Lem_pervasives" 
	 "../../src_ext/lem/isabelle-lib/Lem_set_extra" 
	 "../../src_ext/lem/isabelle-lib/Lem_assert_extra" 
	 "gen_isabelle/Btree"

begin

termination wf_btree by lexicographic_order
termination find_h by lexicographic_order
termination from_to_h by lexicographic_order
termination entries_list_h by lexicographic_order

lemma btree_height_0_is_not_wf: " ((\<forall> e. \<forall> s. \<forall> c.  wf_btree e s c(( 0 :: nat)) \<longleftrightarrow> False))"
by auto

declare entries_list_h.simps [simp del] 
lemma entries_list_h_simps:
"entries_list_h s0 r (Suc h) = (
        (case   s0 r of
          None \<Rightarrow> []
        | Some node \<Rightarrow> (
          (case  node of
            LNode(L(es)) \<Rightarrow> es
          | INode(I(_,qs)) \<Rightarrow> (
            (let list_of_lists_of_entries = (List.map (\<lambda> q .  entries_list_h s0 q h)) qs in
            List.concat list_of_lists_of_entries)
          )
          ))))"
apply (simp add:entries_list_h.simps)
apply (case_tac "s0 r")
apply auto
  apply (case_tac a)
  apply (case_tac inode)
  apply auto
done

lemma wf_btree_requires_qs_length_to_be_at_least_2_if_inodes_exist [simp]:
"\<forall> env k c s r ds qs. 
s r = Some(INode(I(ds,qs))) \<longrightarrow>
(let n = case s r of Some(LNode(L(es))) \<Rightarrow> (length es) | Some(INode(I(_,es))) \<Rightarrow> (length es) | _ \<Rightarrow> 0 in
wf_btree env s (r, set(entries_list_h s r h),n) h \<longrightarrow> (Suc(length ds) = length qs) \<and> (length ds > 0) \<and> (length qs \<ge> 2))"
apply (induct h rule:wf_btree.induct)
  apply auto

  apply (case_tac "Suc (length ds) = length qs")
    apply auto

apply (case_tac ds)
  apply auto
done

lemma if_find_indices_finds_index_then_the_element_exists [simp]:
"\<forall> p n ns. find_indices p list = n # ns \<longrightarrow>
       (\<exists> e . (index list n = Some e) \<and> e \<in> set list \<and> (p e = p (list ! n)) \<and> p e \<and>  p (list ! n)) \<and> n < length list "
apply (induct list)
  apply auto
  
  apply (case_tac "p a")
    apply auto
done

lemma find_h_is_correct_helper [simp]:
"\<forall> k env n ns .find_indices (\<lambda>x. k = entry_to_key env x) list = n # ns \<longrightarrow>
       k = entry_to_key env (list ! n)"
apply (induct list)
  apply auto
done

lemma first_returns_something_only_if [simp]:
"\<forall> p i. first xs p = Some i \<longrightarrow> \<not> (xs = []) \<and> \<not>(i = 0) \<and> (i < Suc (length xs))"
apply auto
apply (simp add:first_def)

apply (simp add:first_def)
apply (case_tac "find_indices p xs")
apply auto

apply (simp add:first_def)
apply (case_tac "find_indices p xs")
  apply auto
done

lemma map_and_first_are_equal [simp]:
"\<forall> k env.
map_of (map (\<lambda>e. (entry_to_key env e, e)) list) k =
(case first list (\<lambda>x. k = entry_to_key env x) of None \<Rightarrow> None | Some i \<Rightarrow> nth_from_1 list i)"
apply auto
apply (induct list)
  (* list = [] *)
  apply (simp add:first_def)

  (* list = a#list *)
  apply (simp add:first_def)
  apply auto
    apply (simp add:nth_from_1_def)
  
    apply (case_tac "map Suc (find_indices (\<lambda>x. k = entry_to_key env x) list)")
      apply auto

      apply (simp add:nth_from_1_def)
done

lemma nth_from_1_is_like_nth [simp]:
"\<forall> list n. (nth_from_1 list 0 = None) \<and> (nth_from_1 list (Suc n) = index list n) "
apply (auto simp add:nth_from_1_def)
done

lemma find_trans_of_None_is_None [simp]:
"\<forall> env p s . find_trans env (None,p,s) = (None,p,s)"
apply (simp add:find_trans_def)
done

lemma find_trans_does_not_alter_store [simp]:
"\<forall> env a q s b' q' s'. (find_trans env (a,q,s)) = (b',q',s') \<longrightarrow> s = s'"
apply auto
apply (simp add:find_trans_def)
apply auto
apply (case_tac "a")
  (* a = None *)
  apply auto

  (* a = Some aa *)
  apply (case_tac "aa")
    (*aa = Find *)
    apply auto
    apply (case_tac "s q")
      (* s q = None *)
      apply auto

      (* s q = Some a *)
      apply (case_tac a)
        apply auto
        apply (case_tac inode)
        apply auto
        apply (case_tac " nth_from_1 b (case first a (key_lt env key) of None \<Rightarrow> length b | Some i \<Rightarrow> i)")
          apply auto
       
        apply (case_tac lnode)
        apply auto
        apply (case_tac "first list (\<lambda>x. key = entry_to_key env x)")
          apply auto
done

lemma find_trans_result_returns_same_elemen_of_store [simp]:
"\<forall> env c p p' s0 s0' r n. 
find_trans env (Some(c),p,s0) = (Some(F_Ret(p',n)),p',s0') \<longrightarrow>
(let page = s0 p in
 let page' = s0' p' in
page = page')
"
apply auto
apply (simp add:find_trans_def)
apply auto
apply (case_tac c)
  (* c = Find *)
  apply auto
  apply (case_tac "s0 p")
    apply auto

    apply (case_tac a)
      apply auto
      apply (case_tac inode)
      apply auto
      apply (case_tac "nth_from_1 b (case first a (key_lt env key) of None \<Rightarrow> length b | Some i \<Rightarrow> i)")
        apply auto

      apply (case_tac lnode)
      apply auto
      apply (case_tac "first list (\<lambda>x. key = entry_to_key env x)")
        apply auto
done        

lemma find_trans_result_returns_f_ret_only_if [simp]:
"\<forall> env c p s0 r n es k. 
find_trans env (Some(c),p,s0) = (Some(F_Ret(p,n)),p,s0) \<longrightarrow>
(case c of
  Find k \<Rightarrow>
( case s0 p of
  Some(LNode(L(es))) \<Rightarrow>
    (case  (first es (\<lambda> x . k = ((entry_to_key   env) x))) of
            Some i => i = n
          | _ => False)
  | _ \<Rightarrow> False)
| _ \<Rightarrow> False)"

apply auto
apply (simp add:find_trans_def)
apply auto
apply (case_tac c)
  (* c = Find *)
  apply auto
  apply (case_tac "s0 p")
    apply auto

    apply (case_tac a)
      apply auto
      apply (case_tac inode)
      apply auto
      apply (case_tac "nth_from_1 b (case first a (key_lt env key) of None \<Rightarrow> length b | Some i \<Rightarrow> i)")
        apply auto

      apply (case_tac lnode)
      apply auto
      apply (case_tac "first list (\<lambda>x. key = entry_to_key env x)")
        apply auto
done

declare find_h.simps [simp del] 

lemma find_h_simps: "
find_h env c (Suc h) = ( (
        (case  c of
          ((Some(F_Ret(p,n)),_,s0)) => (Some(p,n),s0)
        | (_,_,s0) =>
           (let c' = (find_trans env c) in
           find_h env c' ((Suc h)-(1::nat)))
        )))
"
  apply(simp add:find_h.simps )
done

lemma find_h_simps2:
"\<forall> env k ra s va p i. (find_h env (Some (Find k), ra, s) (Suc (Suc va)) = (Some (p, i), s)) = 
(find_h env (find_trans env (Some (Find k), ra, s)) (Suc va) = (Some (p, i), s))"
apply auto
  apply(simp add:find_h_simps Let_def)

  apply(simp add:find_h_simps )
done

lemma find_h_None_is_None [simp]:
"\<forall> env p s . find_h env (None,p,s) h = (None,s)"
apply auto
apply (induct h)
  apply (simp add:find_h.simps)

  apply (simp add:find_h_simps)
done

lemma find_h_of_F_Ret_is_Some [simp]:
"\<forall> env p i s . find_h env ((Some(F_Ret (p,i))),p,s) h = (Some(p,i),s)"
apply (induct h)
  (*h = 0*)
  apply (simp add:find_h.simps)

  (*h = Suc*)
  apply (simp add:find_h_simps)
done

lemma find_h_does_not_alter_store [simp]:
"\<forall> env c0 p0 s0 opt s1. (find_h env (c0,p0,s0) h = (opt,s1)) \<longrightarrow> (s1=s0)"
apply auto
apply (induct h)
apply (simp add:find_h.simps)
  apply auto
  apply (case_tac c0)
    apply auto
      
      apply (case_tac a)
        apply auto

  apply (simp add:find_h_simps)
  apply auto
  apply (case_tac c0)
    (* c0 = None *)
    apply auto
    
    (* c0 = Some a *)
    apply (case_tac a)
      apply auto

      apply (simp add:find_trans_def)
      apply (case_tac "s0 p0")
        apply auto

        apply (case_tac a)
          apply auto
          apply (case_tac inode)
          apply auto
          apply (case_tac "nth_from_1 b (case first a (key_lt env key) of None \<Rightarrow> length b | Some i \<Rightarrow> i)")
            apply auto

          apply (case_tac lnode)
          apply auto
          apply (case_tac "first list (\<lambda>x. key = entry_to_key env x)")
            apply auto
done

lemma find_h_does_not_alter_store_if_wf_btree [simp]:
"\<forall> env c0 p0 s0 opt s1.
let n = case s r of Some(LNode(L(es))) \<Rightarrow> (length es) | Some(INode(I(_,es))) \<Rightarrow> (length es) | _ \<Rightarrow> 0 in
wf_btree env s (r, set(entries_list_h s0 p0 h),n) h \<longrightarrow> (find_h env (c0,p0,s0) h = (opt,s1)) \<longrightarrow> (s1=s0)"
apply auto
done

lemma find_h_always_return_page_id_in_store [simp]:
"\<forall> env k r s0 s i p. find_h env ((Some(Find k)),r,s0) h = (Some(p,i),s) \<longrightarrow> (s = s0) \<and> (p \<in> dom s)"
apply auto
apply (induct h)
  apply (simp add:find_h.simps)

  apply (simp add:find_h_simps)
  apply (simp add:find_trans_def)
    apply (case_tac "s0 r")
      apply auto

      apply (case_tac a)
        apply (case_tac inode)
        apply auto
        apply (case_tac "nth_from_1 b (case first aa (key_lt env k) of None \<Rightarrow> length b | Some i \<Rightarrow> i)")
          apply auto

        apply (case_tac lnode)
        apply auto
        apply (case_tac "first list (\<lambda>x. k = entry_to_key env x)")
          apply auto
done

lemma find_h_returns_some_only_if [simp]:
"\<forall> env c r s p i. find_h env (c,r,s) h = (Some(p,i),s) \<longrightarrow>
(
  (h = 0 \<and> (c = (Some(F_Ret(p,i))))) 
\<or>
  (h > 0 \<and> c = (Some(F_Ret(p,i))))
\<or>
  (\<exists> c'. c' = find_trans env (c,r,s) \<and> find_h env c' (h-(1::nat)) = (Some(p,i),s) )
)
"
apply (case_tac h)
  apply auto
  apply (simp add:find_trans_def Let_def)
  apply (case_tac c)
    apply auto

    apply (simp add:find_h.simps)
    apply (case_tac a)
      apply auto

   apply (simp add:find_h_simps)
   apply auto
   apply (case_tac c)
    apply auto

    apply (case_tac a)
      apply auto
done
  
end
