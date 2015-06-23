theory "BtreeLemmas" 

imports 
 	 Main "~~/src/HOL/Library/Code_Target_Numeral"
	 "../../src_ext/lem/isabelle-lib/Lem_pervasives" 
	 "../../src_ext/lem/isabelle-lib/Lem_set_extra" 
	 "../../src_ext/lem/isabelle-lib/Lem_assert_extra" 
	 "gen_isabelle/Btree"

begin

termination wf_btree by lexicographic_order
termination find_h by lexicographic_order

lemma btree_height_0_is_not_wf: " ((\<forall> e. \<forall> s. \<forall> c.  wf_btree e s c(( 0 :: nat)) \<longleftrightarrow> False))"
by auto

lemma find_trans_does_not_alter_store [simp]:
"(find_trans e (a,q,s)) = (b',q',s') \<Longrightarrow> s = s'"
(* cases of the given configuration *)
apply (case_tac "a")
  (* a = None *)
  apply auto
  apply (simp_all add:find_trans_def)

  (* a = Some aa *)
  apply (case_tac aa)
  apply auto
  (* F_Ret case solved by auto *)

  (* Find case *)
    apply (case_tac "s q")
    apply auto
      (* Inode *)
      apply (case_tac aa)
      apply auto
      apply (case_tac "inode")
      apply auto
      apply (case_tac "nth_from_1 b (first aa (key_lt e key))")
      apply auto

      (* Lnode *)
      apply (case_tac "lnode")
      apply auto
done

lemma find_h_simps: "
find_h env c (Suc h) = ( (
        (case  c of
          ((Some(F_Ret(p,n)),_,s0)) => (Some(p,n),s0)
        | (_,_,s0) =>
           (let c' = (find_trans env c) in
           find_h env c' ((Suc h)-(1::nat)))
        )))
"
  apply(force)
  done

(* the following definitions allow us to not unroll the find_h definition in the inductive case
  of find_h_does_not_alter_store *)
declare find_h.simps [simp del] 
declare find_h_simps [simp add]
lemma find_h_does_not_alter_store [simp]:
"\<forall> env c0 p0 s0 opt s1. (find_h env (c0,p0,s0) h = (opt,s1)) \<longrightarrow> (s1=s0)"
apply (induct h)
  (* h = 0 *)
  apply(auto)
  apply (case_tac c0)
  apply auto

    (* c0 = None  *)
    apply (simp add:find_h.simps)

    (* c0 = Some a *)
    apply (case_tac a)
    apply auto
      (* a = Find *)
      apply (simp add:find_h.simps)
    
      (* a = F_Ret *)
      apply (simp add:find_h.simps)
    
  (* h = Suc nat *)
  apply (case_tac c0)
  apply auto
    (* c0 = None *)
    apply (simp add:find_trans_def)

    apply (case_tac a)
      (* a = F_Ret *)
      apply auto
     
      (* a = Find *)
      apply (simp add:find_trans_def)
      apply (case_tac "s0 p0")
      (* s0 p0 = None *)
      apply auto

      (* s0 p0 = Some a *)
      apply (case_tac a)
        (* a = inode *)
         apply auto
         apply (case_tac inode)
         apply auto
         apply (case_tac " nth_from_1 b (first a (key_lt env key))")
         apply auto

      (* a = lnode *)
      apply (case_tac lnode)
      apply auto
done

lemma find_h_does_not_alter_wf_btree1:
" (wf_btree env s0 (r,ss,n) h) \<and> find_h env (c0,r,s0) h = (Some(p,i),s) \<longrightarrow> (s = s0)"
apply auto
done

lemma find_trans_of_None_is_None [simp]:
"\<forall> env p s . find_trans env (None,p,s) = (None,p,s)"
apply (simp add:find_trans_def)
done

lemma find_h_of_None_is_None [simp]:
"\<forall> env p s . find_h env (None,p,s) h = (None,s)"
apply (induct h)
  (*h = 0*)
  apply (simp add:find_h.simps)

  (*h = Suc*)
  apply auto
done

lemma find_h_of_F_Ret_is_Some [simp]:
"\<forall> env p i s . find_h env ((Some(F_Ret (p,i))),p,s) h = (Some(p,i),s)"
apply (induct h)
  (*h = 0*)
  apply (simp add:find_h.simps)

  (*h = Suc*)
  apply auto
done

    
lemma if_find_trans_returns_None_find_h_returns_None [simp]:
"\<forall> env p s . find_trans env (c,p,s) = (None,p,s) \<longrightarrow> find_h env (c,p,s) h = (None,s)"
apply auto
  apply (induct h)
  (* h = 0 *)
    apply (case_tac c)
    (* c = None *)
    apply (simp add:find_h.simps)

    (* c = Some a *)
    apply (simp add:find_trans_def)
    apply auto
    apply (case_tac a)
      (* a = F_Ret *)
      apply auto

      (* a = Find *)
      apply (case_tac "s p")

        (* s p = None *)
        apply (simp add:find_h.simps)

        (* s p = Some a *)
        apply (case_tac a)
        apply auto
          (* a = inode *)
          apply (case_tac inode)
          apply auto
          apply (case_tac "nth_from_1 b (first a (key_lt env key))")
          apply auto
          apply (simp add:find_h.simps)

          (* a = lnode *)
          apply (case_tac lnode)
          apply auto

  (* h = Suc *)
  apply (case_tac c)
    (* c = None *)
    apply auto

    (* c = Some a *)
    apply (case_tac a)
    apply auto
    apply (simp add:find_trans_def)
done

lemma find_h_always_return_page_id_in_store [simp]:
"\<forall> env k r s0 s i p. find_h env ((Some(Find k)),r,s0) h = (Some(p,i),s) \<longrightarrow> (s = s0) \<and> (p \<in> dom s)"
apply auto
  (* the page_id obtained by find is in the store *)
  apply (induct h)
    (* h = 0 *)
    apply auto
    apply (simp add:find_h.simps)

    (* h = Suc h *)
    apply (simp add:find_trans_def)
    apply (case_tac "s0 r")
      (* s0 r = None *)
      apply auto

      (* s0 r = Some a *)
      apply (case_tac a)
      apply auto
      apply (case_tac inode)
      apply auto
      apply (case_tac "nth_from_1 b (first a (key_lt env k))")
      apply auto

      apply (case_tac lnode)
      apply (auto)
      apply (simp add:find_h.simps)
      apply (case_tac h)
      apply auto
done 

(*lemma find_h_always_return_page_id_in_store1 [simp]:
"\<forall> env k r s i p ss n. (find_h env ((Some(Find k)),r,s) h = (Some(p,i),s) \<and> (wf_btree env s (r,ss,n) h) ) \<longrightarrow> (p \<in> dom s)"
apply auto
apply (induct h rule:wf_btree.induct)
  (* h = 0 *)
  apply auto
  apply (simp add:find_trans_def)
  apply (case_tac "s ra")
    (* s r = None *)
    apply auto

    (* s r = Some a *)
    apply (case_tac a)
      (* a= inode *)
      apply auto

      apply (case_tac lnode)
      apply auto
      apply (simp add:find_h.simps)

      (* h = Suc *)
      apply (case_tac "s ra")
        (* s ra = None *)
        apply auto

        apply (case_tac a)
          (* a = lnode *)
          apply auto

          (* a = inode *)
          apply (case_tac inode)
          apply auto
          apply (case_tac "n = length b \<and> Suc (length a) = length b")
            apply auto

            apply (case_tac a)
            apply auto

oops*)

lemma find_h_is_correct:
"\<forall> env s r ss n k p i es. find_h env ((Some(Find k)),r,s) h = (Some(p,i),s) \<longrightarrow> (p \<in> dom s) 
\<and> (case (s p) of (Some(LNode(L(es)))) \<Rightarrow> (case (nth_from_1 es i) of Some e \<Rightarrow> (e \<in> (entry_set s p)) \<and> (k = (entry_to_key env e)) | _ \<Rightarrow> True) | _ \<Rightarrow> False)"
apply auto
  (* the page_id obtained by find is in the store *)
  apply (induct h)
    (* h = 0 *)
    apply (case_tac "s p")
      (* s p = None*)
      apply (simp add:find_h.simps)

      apply (case_tac a)
        (* a = inode *)
        apply auto
        apply (simp add:find_h.simps)

        (* a = lnode*)
        apply (simp add:find_h.simps)

    (* h = Suc h *)
    apply (simp add:find_trans_def)
    apply (case_tac "s r")
      apply auto

      apply (case_tac a)
        apply auto
        apply (case_tac inode)
        apply auto
        apply (case_tac "nth_from_1 b (first a (key_lt env k))")
        apply auto

        apply (case_tac lnode)
        apply auto
        apply (case_tac "nth_from_1 list (first list (\<lambda>x. key_lte env k (entry_to_key env x)))")
        apply auto
        

        (* we have only find_h on F_Ret in the recursive call *)
        apply (simp add:find_h.simps)
        apply auto
        apply (case_tac h)
          apply auto
          apply (case_tac "nth_from_1 list (first list (\<lambda>x. key_lte env k (entry_to_key env x)))")
          apply auto
          apply (case_tac "s p")
          apply auto
          apply (case_tac a)
          apply auto


done


(* this lemma is not useful as it is.
  We would like to show that find_entry behaves as a map look up.
  The map should be from key to entry. (for this we need to define an op that translates the btree in a map?)
  The key in the configuration passed to find_h is fundamental to state the equality. (the lemma should be something like: find_h_stuff = k m)
*)
lemma find_entry_equal_to_map:
"\<forall> env c h p i s . ((find_h env c h) = (Some(p,i),s)) \<longrightarrow> (find_entry (Some(p,i),s) = (case s p of (Some(LNode(L es))) \<Rightarrow> Some(nth_from_1 es i) | _ \<Rightarrow> None)) "
apply (simp add:find_entry.simps)
done
end
