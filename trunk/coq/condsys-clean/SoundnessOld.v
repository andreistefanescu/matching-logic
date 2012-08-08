(*     assert (HWD : WeaklyWD (phi, phi', side)) by (apply H; apply H0). *)
(*     clear H. *)
(*     unfold WeaklyWD in *. *)
(*     unfold WeaklyWDPattern in *. *)

(*     splitAnd HWD Hsat' Hside. simpl in *. *)
(*     specialize (Hsat' rho). *)
(*     elim Hsat'; intros gamma' Htemp; clear Hsat'; rename Htemp into Hsat'. *)
(*     exists gamma'. *)
(*     split. *)

(*     constructor. *)
(*     constructor. *)
(*     eapply TSIntro. *)
(*     apply H0. *)
(*     simpl. *)
(*     rewrite <- SatAnd in Hsat. *)
(*     apply Hsat. *)
(*     simpl. *)
(*     apply Hsat'. *)
(*     simpl in *. *)

(*     assert (Hsideh : forall side', side' SuffixOf side -> *)
(*       List.Forall (fun srule => RhoStronglyValid rho srule) side'). *)
(*     induction side'. *)
(*     intros Hnil; inversion Hnil; subst side; constructor. *)
(*     rewrite Forall_forall in *. *)
(*     intros. *)
(*     inversion H2. *)
(*     subst a. *)

(*     unfold RhoStronglyValid. *)
(*     unfold GStronglyValid in *. *)
(*     assert (Htemp : In x side). *)
(*     eapply SuffixHeadIn. apply H. *)
(*     specialize (Hind x Htemp). *)

(*     intros. *)
(*     assert (Hsucceq : gamma SuccEq gamma0). *)
(*     unfold TerminationDependence. *)
(*     apply clos_step. *)
(*     right. *)
(*     exists (phi, phi', side). *)
(*     split. *)
(*     assumption. *)
(*     exists rho. *)
(*     exists side'. *)
(*     exists x. *)
(*     split. *)
(*     assumption. *)
(*     split. *)
(*     simpl. *)
(*     rewrite <- SatAnd in Hsat; apply Hsat. *)
(*     split. *)
(*     rewrite Forall_forall. *)

    
    
(*     apply IHside'. *)
(*     eapply SuffixWeaken. apply H. apply H3. *)
    
(*     specialize (IHside H0 Hind). *)

(*     intros. *)
    
(*     generalize dependent side. *)
(*     generalize dependent gammaList. *)
    


(*     assert (Hind : forall srule : SimpleRule, *)
(*       In srule side -> *)
(*       GStronglyValid false (And (fst srule) psi, snd srule) g). *)
(*     intros. *)
(*     specialize (H3 srule H1). *)
(*     apply H3; try assumption. *)
(*     inversion Hempty. *)
(*     unfold ssysUnion. *)
(*     rewrite app_nil_r. *)
(*     assumption. *)
(*     constructor. *)
(*     unfold ssysEmpty. *)
(*     unfold IsEmpty. *)
(*     reflexivity. *)
(*     clear H3. *)

(*     apply ExistsList. *)
(*     intros. *)
   
(*     assert (Hexists : exists srule, *)
(*       (In srule side /\ Satisfies elem rho (fst srule))). *)
(*     eapply SatisfiesListIn. *)
(*     apply H. *)
(*     assumption. *)
(*     elim Hexists; intros. *)
(*     rewrite Forall_forall in Hside. *)
(*     specialize (Hside (fst x)). *)
    
(*     assert (Htemp : In (fst x) (mapFst side)). *)
(*     apply InProjectFst; apply H2. *)
(*     specialize (Hside Htemp rho). *)
(*     clear Htemp. *)
(*     elim Hside; intros. *)
(*     specialize (Hind x (proj1 H2)). *)
(*     unfold GStronglyValid in Hind. *)
(*     rename x into srule. *)
(*     assert (gamma SuccEq x0). *)
(*     eapply clos_step. *)
(*     unfold TerminationDependence. *)
(*     right. *)
(*     exists (phi, phi', side). *)
(*     intros. *)
(*     exists rho. *)
(*     exists  *)


(*     HgSuccEqgamma rho). *)
(*     rewrite <- SatAnd in *. *)
(*     splitAnd Hsat Hsat1 Hsat2. *)
    
(*     assert (Htemp : Satisfies gamma rho (fst (And (fst x) psi, snd x))). *)
(*     simpl in *. *)
(*     apply SatAnd. *)
(*     split. *)
    
    

(*     assert (HsideT : forall srule : SimpleRule, In srule side -> *)
(*       GStronglyValid false srule g). *)
(*     eapply GStronglyValidWeakenAnd. *)

(*     induction side. *)
(*     exists nil. *)
(*     inversion H. *)
(*     constructor. *)
    

(*     assert (Hside : forall side', side' suffix_of side -> *)
(*       List.Forall (fun srule => rho_valid_srule srule rho (ts S)) side'). *)

(*   induction side'. *)
(*   rewrite List.Forall_forall. *)
(*   intros. *)
(*   exfalso. *)
(*   apply (List.in_nil H4). *)
  
(*   rewrite List.Forall_forall. *)
(*   intros. *)
(*   destruct H4. *)
(*   rewrite H4 in *. *)

(*   unfold rho_valid_srule. *)
(*   intros gamma_i' Hgamma_i'. *)

(*   assert (Hless' : less_than S gamma_i' gamma'). eapply belea'. apply H. apply eq_refl. apply H3. *)
(*   eapply belea'''. apply HT. apply Hless. *)
(*   simpl in Hgamma'. *)
(*   rewrite <- SatAnd in Hgamma'. *)
(*   apply Hgamma'. *)
(*   apply IHside'. *)
(*   eapply suffix_weaken. *)
(*   apply H3. *)
(*   assumption. *)
  
(*   assert (Hsound_i' : GStronglyValidssys true (union_ssys A C) gamma_i'). *)
  
(*   unfold GStronglyValidssys. *)
(*   intro ruleAC. *)
(*   intro Hin. *)
(*   unfold union_ssys in *. *)
(*   rewrite List.in_app_iff in Hin. *)
(*   inversion Hin. *)
  
(*   unfold GStronglyValidssys in HA. *)
(*   eapply sound_weaken'. *)
(*   apply HA. *)
(*   destruct ruleAC; simpl; assumption. *)
(*   eapply clos_trans. apply clos_step. apply Hless'. assumption. *)
  
(*   unfold GStronglyValidssys in HA. *)
(*   eapply sound_weaken'. *)
(*   apply HC. *)
(*   eapply trans_help. apply Hless. apply clos_step. apply Hless'. *)
  
(*   destruct ruleAC; simpl; assumption. *)
(*   apply clos_refl. *)

(*   subst a. *)
(*   rename x into rule. *)
  
(*   assert (Hrule_side : List.In rule side). *)
(*   eapply suffix_of_implies_in. *)
(*   apply H3. *)

(*   specialize (H2 rule Hrule_side gamma_i'). *)
  
(*   assert (Hterm_i' : gamma_i' optermin S). *)
(*   eapply belea'''. apply HT. eapply clos_trans. apply clos_step. apply Hless'. apply Hless. *)
(*   specialize (H2 Hterm_i' Hsound_i'). *)
  
(*   assert (Hcool : gamma_almost_ssys true empty_ssys gamma_i'). *)
(*   unfold gamma_almost_ssys. *)
(*   unfold empty_ssys. *)
(*   intros. *)
(*   unfold GStronglyValidssys. *)
(*   intros. *)
(*   exfalso; apply H5. *)
  
(*   specialize (H2 Hcool). *)
(*   decompose [and] H2. *)
(*   assert (is_empty empty_ssys). *)
(*   unfold is_empty. unfold empty_ssys. trivial. *)
(*   specialize (H4 H6). *)
(*   unfold GStronglyValid in H4. *)
(*   specialize (H4 gamma_i'). *)
(*   specialize (H4 (clos_refl _ _ _)). *)
(*   specialize (H4 rho). *)
  
(*   assert (Satisfies gamma_i' rho (fst (And (fst rule) psi, snd rule))). *)
(*   apply SatAnd. *)
(*   split. *)
(*   assumption. *)
(*   eapply stateless_sat. *)
(*   assumption. simpl in Hgamma'. *)
(*   rewrite <- SatAnd in Hgamma'. *)
(*   apply Hgamma'. *)
  
(*   specialize (H4 H7). *)
(*   elim H4; intros. *)
(*   exists x. *)
(*   split. *)
(*   simpl in H8. *)
(*   apply H8. apply H8. *)

(*   assert (Hside'_suffix_of_side : side' suffix_of side). *)
(*   eapply suffix_weaken. *)
(*   apply H3. *)
(*   specialize (IHside' Hside'_suffix_of_side). *)
(*   simpl in H4. *)
(*   rewrite List.Forall_forall in IHside'. *)
(*   specialize (IHside' x). *)
(*   specialize (IHside' H4). *)
(*   assumption. *)

(*   simpl in Hgamma'. *)
(*   rewrite <- SatAnd in Hgamma'. *)
(*   decompose [and] Hgamma'. *)
  
(*   assert (H_wd : well_defined (srule, side)) by (apply (well_defined_S _ H)). *)
(*   unfold well_defined in H_wd. *)
(*   simpl in H_wd. *)
(*   specialize (H_wd gamma' rho H3). *)
  
(*   assert (Hsidenew: rho_valid_ssys side rho (ts S)). *)
(*   unfold rho_valid_ssys. *)

(*   specialize (Hside side (here side)). *)
(*   apply Hside. *)
  
(*   specialize (H_wd Hsidenew). *)
  
(*   elim H_wd; intros. *)
(*   exists x. *)
(*   split. apply clos_unstrict. apply H5. *)
(*   simpl. rewrite <- SatAnd. *)
(*   split. apply H5. *)
(*   eapply stateless_sat. assumption. apply H4. *)
  
(*   SCase "non-empty circularities". *)
  

(*   unfold GStronglyValid. *)
(*   intros gamma' Hless rho Hgamma'. *)

(*   assert (Hside : forall side', side' suffix_of side -> *)
(*     List.Forall (fun srule => rho_valid_srule srule rho (ts S)) side'). *)
(*   induction side'. *)
(*   rewrite List.Forall_forall. *)
(*   intros. *)
(*   exfalso. *)
(*   apply (List.in_nil H4). *)
  
(*   rewrite List.Forall_forall. *)
(*   intros. *)
(*   destruct H4. *)
(*   rewrite H4 in *. *)

(*   unfold rho_valid_srule. *)
(*   intros gamma_i' Hgamma_i'. *)

(*   assert (Hless' : less_than S gamma_i' gamma'). eapply belea'. apply H. apply eq_refl. apply H3. *)
(*   eapply belea'''. apply HT. apply Hless. *)
(*   simpl in Hgamma'. *)
(*   rewrite <- SatAnd in Hgamma'. *)
(*   apply Hgamma'. *)
(*   apply IHside'. *)
(*   eapply suffix_weaken. *)
(*   apply H3. *)
(*   assumption. *)
  
(*   assert (Hsound_i' : GStronglyValidssys true (union_ssys A C) gamma_i'). *)
  
(*   unfold GStronglyValidssys. *)
(*   intro ruleAC. *)
(*   intro Hin. *)
(*   unfold union_ssys in *. *)
(*   rewrite List.in_app_iff in Hin. *)
(*   inversion Hin. *)
  
(*   unfold GStronglyValidssys in HA. *)
(*   eapply sound_weaken'. *)
(*   apply HA. *)
(*   destruct ruleAC; simpl; assumption. *)
(*   eapply clos_trans. apply clos_step. apply Hless'. assumption. *)
  
(*   unfold GStronglyValidssys in HA. *)
(*   eapply sound_weaken'. *)
(*   apply HC. *)
(*   eapply trans_help. apply Hless. apply clos_step. apply Hless'. *)
  
(*   destruct ruleAC; simpl; assumption. *)
(*   apply clos_refl. *)

(*   subst a. *)
(*   rename x into rule. *)
  
(*   assert (Hrule_side : List.In rule side). *)
(*   eapply suffix_of_implies_in. *)
(*   apply H3. *)

(*   specialize (H2 rule Hrule_side gamma_i'). *)
  
(*   assert (Hterm_i' : gamma_i' optermin S). *)
(*   eapply belea'''. apply HT. eapply clos_trans. apply clos_step. apply Hless'. apply Hless. *)
(*   specialize (H2 Hterm_i' Hsound_i'). *)
  
(*   assert (Hcool : gamma_almost_ssys true empty_ssys gamma_i'). *)
(*   unfold gamma_almost_ssys. *)
(*   unfold empty_ssys. *)
(*   intros. *)
(*   unfold GStronglyValidssys. *)
(*   intros. *)
(*   exfalso; apply H5. *)
  
(*   specialize (H2 Hcool). *)
(*   decompose [and] H2. *)
(*   assert (is_empty empty_ssys). *)
(*   unfold is_empty. unfold empty_ssys. trivial. *)
(*   specialize (H4 H6). *)
(*   unfold GStronglyValid in H4. *)
(*   specialize (H4 gamma_i'). *)
(*   specialize (H4 (clos_refl _ _ _)). *)
(*   specialize (H4 rho). *)
  
(*   assert (Satisfies gamma_i' rho (fst (And (fst rule) psi, snd rule))). *)
(*   apply SatAnd. *)
(*   split. *)
(*   assumption. *)
(*   eapply stateless_sat. *)
(*   assumption. simpl in Hgamma'. *)
(*   rewrite <- SatAnd in Hgamma'. *)
(*   apply Hgamma'. *)
  
(*   specialize (H4 H7). *)
(*   elim H4; intros. *)
(*   exists x. *)
(*   split. *)
(*   simpl in H8. *)
(*   apply H8. apply H8. *)

(*   assert (Hside'_suffix_of_side : side' suffix_of side). *)
(*   eapply suffix_weaken. *)
(*   apply H3. *)
(*   specialize (IHside' Hside'_suffix_of_side). *)
(*   simpl in H4. *)
(*   rewrite List.Forall_forall in IHside'. *)
(*   specialize (IHside' x). *)
(*   specialize (IHside' H4). *)
(*   assumption. *)

(*   simpl in Hgamma'. *)
(*   rewrite <- SatAnd in Hgamma'. *)
(*   decompose [and] Hgamma'. *)
  
(*   assert (H_wd : well_defined (srule, side)) by (apply (well_defined_S _ H)). *)
(*   unfold well_defined in H_wd. *)
(*   simpl in H_wd. *)
(*   specialize (H_wd gamma' rho H3). *)
  
(*   assert (Hsidenew: rho_valid_ssys side rho (ts S)). *)
(*   unfold rho_valid_ssys. *)

(*   specialize (Hside side (here side)). *)
(*   apply Hside. *)
  
(*   specialize (H_wd Hsidenew). *)
  
(*   elim H_wd; intros. *)
(*   exists x. *)
(*   split. apply H5. *)
(*   simpl. rewrite <- SatAnd. *)
(*   split. apply H5. *)
(*   eapply stateless_sat. assumption. apply H4. *)
    
(*   Case "Axiom A". *)
  
(*   intros; split; intro HemptyC ; *)
(*     (unfold GStronglyValid; simpl; intros gamma' Hless rho Hsat'; *)
(*       assert (Hsrule : GStronglyValid true srule gamma) by (apply H2; assumption); *)
(*         rewrite <- SatAnd in Hsat'; decompose [and] Hsat'; *)
(*           unfold GStronglyValid in Hsrule; *)
(*             specialize (Hsrule gamma' Hless rho H4); *)
(*               elim Hsrule; intros gamma''; intros; decompose [and] H6; *)
(*                 exists gamma''; split; [ try apply clos_unstrict; assumption | *)
(*                   apply SatAnd; split ; [ apply H8 | eapply stateless_sat ; [ apply H0 | apply H5 ]]]). *)
  
(*   Case "Reflexivity". *)
(*   intros. split; intros HemptyC. *)
  
(*   SCase "C is empty". *)
(*   unfold GStronglyValid; simpl; intros; exists gamma'; split ; [ apply clos_refl | assumption ]. *)
  
(*   SCase "C is not empty". *)
(*   unfold is_empty in HemptyC. unfold empty_ssys in HemptyC. *)
(*   assert (forall rule : SimpleRule, List.In rule nil -> False). *)
(*   apply List.in_nil. *)
(*   tauto. *)
  
(*   Case "Transitivity". *)
(*   intros gamma HT HA HC; split; intros HemptyC. *)
  
(*   SCase "C is empty". *)
  
(*   specialize (IHPS1 gamma HT HA HC). *)
(*   specialize (IHPS2 gamma HT). *)
  
(*   assert (HA' : GStronglyValidssys true (union_ssys A C) gamma). *)
(*   eapply sound_union. apply HA. *)
(*   unfold GStronglyValidssys; unfold is_empty in HemptyC; intros; exfalso; eapply HemptyC. apply H1. *)
(*   reflexivity. *)
  
(*   assert (HC' : gamma_almost_ssys true empty_ssys gamma). *)
(*   unfold gamma_almost_ssys; unfold empty_ssys; firstorder. *)
  
(*   specialize (IHPS2 HA' HC'). *)
(*   decompose [and] IHPS1. decompose [and] IHPS2. *)
(*   eapply gamma_sound_trans. apply H1. assumption. apply H3. *)
(*   unfold is_empty. unfold empty_ssys. tauto. *)
(*   compute. reflexivity. *)
  
(*   SCase "C is not empty". *)
(*   specialize (IHPS1 gamma HT HA HC). *)
(*   unfold GStronglyValid. *)
(*   intros gamma1 Htransition rho Hsat. *)
(*   decompose [and] IHPS1. *)
(*   clear H1. *)
(*   clear IHPS1. *)
(*   rename H2 into Hind1. *)
(*   specialize (Hind1 HemptyC). *)
(*   unfold GStronglyValid in Hind1. *)
(*   specialize (Hind1 gamma1 Htransition rho Hsat). *)
(*   elim Hind1; intros gamma2; intros. *)
(*   decompose [and] H1. *)
(*   clear H1. *)
(*   rename H2 into Htrans2. *)
(*   rename H3 into Hsat2. *)
(*   specialize (IHPS2 gamma2). *)
  
(*   assert (Hlt2 : clos M (less_than S) true gamma2 gamma). *)
(*   eapply clos_cat'. *)
(*   apply ts_to_lt. *)
(*   apply Htrans2. *)
(*   apply Htransition. *)
(*   compute. reflexivity. *)
  
(*   assert (HT2 : gamma2 optermin S). *)
(*   eapply belea'''. *)
(*   apply HT. *)
(*   apply Hlt2. *)
(*   specialize (IHPS2 HT2). *)
  
(*   assert (Hsound2 : GStronglyValidssys true (union_ssys A C) gamma2). *)
(*   eapply sound_union. *)
(*   SSCase "sound w.r.t. A". *)
(*   unfold GStronglyValidssys. *)
(*   intros. *)
(*   eapply sound_weaken'. *)
(*   apply HA. *)
(*   destruct srule; simpl; apply H1. *)
(*   apply clos_unstrict. *)
(*   assumption. *)
  
(*   SSCase "sound w.r.t. C". *)
(*   unfold gamma_almost_ssys in HC. *)
(*   apply HC. *)
(*   assumption. *)
(*   reflexivity. *)
(*   specialize (IHPS2 Hsound2). *)
  
  
(*   assert (Hemptysound : gamma_almost_ssys true empty_ssys gamma2). *)
(*   unfold gamma_almost_ssys. *)
(*   unfold empty_ssys. *)
(*   intros. *)
(*   unfold GStronglyValidssys. *)
(*   intros. *)
(*   exfalso. assumption. *)
(*   specialize (IHPS2 Hemptysound). *)
(*   decompose [and] IHPS2. *)
(*   clear H2. *)
(*   clear IHPS2. *)
(*   rename H1 into Hind2. *)
  
(*   assert (Hemptyempty : is_empty empty_ssys). *)
(*   compute; intros; exfalso; assumption. *)
(*   specialize (Hind2 Hemptyempty). *)
  
(*   unfold GStronglyValid in Hind2. *)
(*   simpl in Hind2. *)
(*   simpl. *)
(*   specialize (Hind2 gamma2). *)
(*   specialize (Hind2 (clos_refl _ _ _)). *)
(*   specialize (Hind2 rho). *)
(*   specialize (Hind2 Hsat2). *)
(*   elim Hind2. intros gamma3. intros Hand. *)
(*   decompose [and] Hand. *)
(*   exists gamma3. *)
(*   split. *)
(*   eapply clos_cat''. *)
(*   apply Htrans2. *)
(*   apply H1. *)
(*   compute. right. reflexivity. *)
(*   assumption. *)
  
(*   Case "Consequence". *)
(*   rename H into V1. *)
(*   rename H1 into V2. *)
(*   intros gamma HT HA HC. *)
(*   specialize (IHPS gamma HT HA HC). *)
(*   decompose [and] IHPS. *)
(*   rename H into HeC. *)
(*   rename H1 into HneC. *)
(*   split; intro Hemptyness. *)
  
(*   SCase "C is empty". *)
(*   specialize (HeC Hemptyness). *)
(*   unfold GStronglyValid. *)
(*   intros gamma' Htrans rho Hsat. *)
(*   unfold Valid in V1. *)
(*   specialize (V1 gamma' rho). *)
(*   rewrite <- SatImplies in V1. *)
(*   specialize (V1 Hsat). *)
(*   unfold GStronglyValid in HeC. *)
(*   specialize (HeC gamma' Htrans rho V1). *)
(*   elim HeC; intros gamma'' Hand. *)
(*   decompose [and] Hand; clear Hand; rename H into Htrans'; *)
(*     rename H1 into Hsat'. *)
(*   unfold Valid in V2. *)
(*   specialize (V2 gamma'' rho). *)
(*   rewrite <- SatImplies in V2. *)
(*   specialize (V2 Hsat'). *)
(*   exists gamma''. *)
(*   split; assumption. *)
  
(*   SCase "C not empty". *)
(*   specialize (HneC Hemptyness). *)
(*   unfold GStronglyValid. *)
(*   intros gamma' Htrans rho Hsat. *)
(*   unfold Valid in V1. *)
(*   specialize (V1 gamma' rho). *)
(*   rewrite <- SatImplies in V1. *)
(*   specialize (V1 Hsat). *)
(*   unfold GStronglyValid in HeC. *)
(*   specialize (HneC gamma' Htrans rho V1). *)
(*   elim HneC; intros gamma'' Hand. *)
(*   decompose [and] Hand; clear Hand; rename H into Htrans'; *)
(*     rename H1 into Hsat'. *)
(*   unfold Valid in V2. *)
(*   specialize (V2 gamma'' rho). *)
(*   rewrite <- SatImplies in V2. *)
(*   specialize (V2 Hsat'). *)
(*   exists gamma''. *)
(*   split; assumption. *)
  
(*   Case "Case analysis". *)
(*   intros gamma HT HA HC. *)
(*   specialize (IHPS1 gamma HT HA HC). *)
(*   specialize (IHPS2 gamma HT HA HC). *)
(*   decompose [and] IHPS1. *)
(*   decompose [and] IHPS2. *)
(*   clear IHPS1. *)
(*   clear IHPS2. *)
(*   rename H1 into He1. *)
(*   rename H2 into Hne1. *)
(*   rename H3 into He2. *)
(*   rename H4 into Hne2. *)
(*   split. *)
(*   SCase "empty C". *)
(*   intros Hempty. *)
(*   specialize (He1 Hempty). *)
(*   specialize (He2 Hempty). *)
(*   unfold GStronglyValid. *)
(*   intros gamma' Htrans rho Hsat. *)
(*   simpl in Hsat. *)
(*   rewrite <- SatOr in Hsat. *)
(*   destruct Hsat. *)
(*   unfold GStronglyValid in He1. *)
(*   specialize (He1 gamma' Htrans rho H1). *)
(*   elim He1; intros gamma'' Hand. *)
(*   decompose [and] Hand. *)
(*   exists gamma'' ; split; assumption. *)
(*   unfold GStronglyValid in He1. *)
(*   specialize (He2 gamma' Htrans rho H1). *)
(*   elim He2; intros gamma'' Hand. *)
(*   decompose [and] Hand. *)
(*   exists gamma'' ; split; assumption. *)
  
(*   SCase "not empty C". *)
(*   intros Hempty. *)
(*   specialize (Hne1 Hempty). *)
(*   specialize (Hne2 Hempty). *)
(*   unfold GStronglyValid. *)
(*   intros gamma' Htrans rho Hsat. *)
(*   simpl in Hsat. *)
(*   rewrite <- SatOr in Hsat. *)
(*   destruct Hsat. *)
(*   unfold GStronglyValid in He1. *)
(*   specialize (Hne1 gamma' Htrans rho H1). *)
(*   elim Hne1; intros gamma'' Hand. *)
(*   decompose [and] Hand. *)
(*   exists gamma'' ; split; assumption. *)
(*   unfold GStronglyValid in He1. *)
(*   specialize (Hne2 gamma' Htrans rho H1). *)
(*   elim Hne2; intros gamma'' Hand. *)
(*   decompose [and] Hand. *)
(*   exists gamma'' ; split; assumption. *)
  
(*   Case "abstraction". *)
(*   intros gamma HT HA HC; split; intros Hempty. *)
(*   SCase "empty C". *)
(*   unfold GStronglyValid. *)
(*   intros gamma' Htrans rho Hsat. *)
(*   simpl in Hsat. *)
(*   rewrite <- SatExists in Hsat. *)
(*   elim Hsat; intros gamma0 Hsat0. *)
(*   specialize (IHPS gamma HT HA HC). *)
(*   decompose [and] IHPS. *)
(*   specialize (H1 Hempty). *)
(*   unfold GStronglyValid in H1. *)
(*   specialize (H1 gamma' Htrans (UpdateV rho X gamma0) Hsat0). *)
(*   elim H1; intros gamma'' Hand. *)
(*   decompose [and] Hand. *)
(*   exists gamma''. *)
(*   split. assumption. simpl. simpl in H4. *)
(*   rewrite notFree_sat. apply H4. assumption. *)
  
(*   SCase "not empty C". *)
(*   unfold GStronglyValid. *)
(*   intros gamma' Htrans rho Hsat. *)
(*   simpl in Hsat. *)
(*   rewrite <- SatExists in Hsat. *)
(*   elim Hsat; intros gamma0 Hsat0. *)
(*   specialize (IHPS gamma HT HA HC). *)
(*   decompose [and] IHPS. *)
(*   specialize (H2 Hempty). *)
(*   unfold GStronglyValid in H1. *)
(*   specialize (H2 gamma' Htrans (UpdateV rho X gamma0) Hsat0). *)
(*   elim H2; intros gamma'' Hand. *)
(*   decompose [and] Hand. *)
(*   exists gamma''. *)
(*   split. assumption. simpl. simpl in H4. *)
(*   rewrite notFree_sat. apply H4. assumption. *)
  
(*   Case "Circularity". *)
(*   assert (forall gamma : M, *)
(*     gamma optermin S -> *)
(*     GStronglyValidssys true A gamma -> *)
(*     gamma_almost_ssys true C gamma -> *)
(*     GStronglyValid true (phi, phi') gamma). *)
(*   induction 1. *)
(*   rename x into gamma. *)
(*   assert (gamma optermin S). *)
(*   unfold opterminates; unfold terminates. *)
(*   constructor; assumption. *)
(*   intros HA HC. *)
  
(*   specialize (IHPS gamma H2 HA). *)
  
(*   assert (Htoprove : gamma_almost_ssys true (cons_ssys phi phi' C) gamma). *)
(*   unfold gamma_almost_ssys. *)
(*   unfold cons_ssys. *)
(*   intros. *)
(*   unfold GStronglyValidssys. *)
(*   intros. *)
(*   destruct (List.in_inv H4). *)
(*   destruct H5. *)
(*   apply H1. *)
(*   assumption. *)
(*   unfold GStronglyValidssys; intros. *)
(*   eapply sound_weaken'. *)
(*   destruct srule. *)
(*   apply HA. *)
(*   assumption. *)
(*   apply clos_unstrict. *)
(*   assumption. *)
(*   unfold gamma_almost_ssys. *)
(*   intros. *)
(*   unfold GStronglyValidssys. *)
(*   intros. *)
(*   apply HC. *)
(*   eapply clos_cat''. *)
(*   apply H5. apply H3. *)
(*   compute. right. reflexivity. *)
(*   assumption. *)
(*   apply HC. *)
(*   assumption. *)
(*   assumption. *)
  
(*   specialize (IHPS Htoprove). *)
(*   decompose [and] IHPS. *)
(*   clear IHPS. *)
(*   clear H3. *)
  
(*   assert (Htoprove2 :  ~ is_empty (cons_ssys phi phi' C)). *)
(*   unfold is_empty. *)
(*   unfold cons_ssys. *)
(*   unfold not. *)
(*   intros. *)
(*   eapply H3. *)
(*   left. reflexivity. *)
  
(*   specialize (H4 Htoprove2). *)
(*   assumption. *)
  
(*   intros. *)
(*   split. *)
(*   intros. *)
(*   specialize (H0 gamma H1 H2 H3). *)
(*   apply sound_unstrict. *)
(*   intros. *)
(*   apply H0; assumption. *)
(*   intros. *)
(*   apply H0; assumption. *)
(* Qed. *)
