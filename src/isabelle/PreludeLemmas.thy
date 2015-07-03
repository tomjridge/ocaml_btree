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

lemma btree_height_0_is_not_wf: " ((\<forall> e. \<forall> s. \<forall> c.  wf_btree e s c(( 0 :: nat)) \<longleftrightarrow> False))"
by auto

lemma first_returns_something_only_if [simp]:
"\<forall> xs p i. first xs p = Some i \<longrightarrow> \<not> (xs = []) \<and> \<not>(i = 0) \<and> (i < Suc (length xs))"
apply auto
apply (simp add:first_def)

apply (simp add:first_def)
apply (case_tac "find_indices p xs")
apply auto

apply (simp add:first_def)
apply (case_tac "find_indices p xs")
  apply auto
  apply (case_tac xs)
    apply auto
    
oops
lemma ab [simp]:
"\<forall> a p lista. find_indices p list = a # lista \<longrightarrow> (
       case index list a of None \<Rightarrow> False | Some e \<Rightarrow> True)"
apply auto
apply (induct list)
  apply auto
  
  apply (case_tac "p a")
    apply auto
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
        apply (case_tac " nth_from_1 b (case first a (key_lt env key) of None \<Rightarrow> length a + 1 | Some i \<Rightarrow> i)")
          apply auto
       
        apply (case_tac lnode)
        apply auto
        apply (case_tac "first list (\<lambda>x. key_eq env key (entry_to_key env x))")
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
      apply (case_tac "nth_from_1 b (case first a (key_lt env key) of None \<Rightarrow> length a + 1 | Some i \<Rightarrow> i)")
        apply auto

      apply (case_tac lnode)
      apply auto
      apply (case_tac "first list (\<lambda>x. key_eq env key (entry_to_key env x))")
        apply auto
done        

lemma find_trans_result_returns_f_ret_only_if [simp]:
"\<forall> env c p s0 r n es k. 
find_trans env (Some(c),p,s0) = (Some(F_Ret(p,n)),p,s0) \<longrightarrow>
(case c of
  Find k \<Rightarrow>
( case s0 p of
  Some(LNode(L(es))) \<Rightarrow>
    (case  (first es (\<lambda> x .  key_eq env k ((entry_to_key   env) x))) of
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
      apply (case_tac "nth_from_1 b (case first a (key_lt env key) of None \<Rightarrow> length a + 1 | Some i \<Rightarrow> i)")
        apply auto

      apply (case_tac lnode)
      apply auto
      apply (case_tac "first list (\<lambda>x. key_eq env key (entry_to_key env x))")
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
          apply (case_tac "nth_from_1 b (case first a (key_lt env key) of None \<Rightarrow> length a + 1 | Some i \<Rightarrow> i)")
            apply auto

          apply (case_tac lnode)
          apply auto
          apply (case_tac "first list (\<lambda>x. key_eq env key (entry_to_key env x))")
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
        apply (case_tac "nth_from_1 b (case first aa (key_lt env k) of None \<Rightarrow> length aa + 1 | Some i \<Rightarrow> i)")
          apply auto

        apply (case_tac lnode)
        apply auto
        apply (case_tac "first list (\<lambda>x. key_eq env k (entry_to_key env x))")
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
