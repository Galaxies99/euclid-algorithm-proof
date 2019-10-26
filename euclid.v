Require Import Coq.ZArith.ZArith.
Local Open Scope Z.

Inductive Euclid: Z * Z -> Z * Z -> Prop :=
| Euclid_refl: forall x y, Euclid (x, y) (x, y)
| Euclid_step: forall x y u v, Euclid (x, y) (u, v) ->
                               v <> 0 ->
                               Euclid (x, y) (v, Z.rem u v).

Lemma Euclid_invariant1: forall x y u v d,
  Euclid (x, y) (u, v) ->
  (d | u) /\ (d | v) ->
  (d | x) /\ (d | y).
Proof.
  intros.
  remember (u, v) as uv eqn: ?H.
  remember (x, y) as xy eqn: ?H.
  revert u v x y H0 H1 H2.
  induction H; intros.
  - inversion H2. inversion H1. subst x0 y0. subst. assumption.
  - inversion H3. inversion H2. subst x0 y0 u0 v0. clear H2 H3.
    specialize IHEuclid with (u0 := u) (v0 := v).
    apply IHEuclid; auto.
    + destruct H1 as [?H ?H].
      unfold Z.divide in *.
      destruct H1 as [z1 ?H].
      destruct H2 as [z2 ?H].
      split.
      * exists (u ÷ v * z1 + z2).
        Search ((_ + _) * _).
        rewrite Z.mul_add_distr_r.
        rewrite <- Z.mul_assoc. 
        rewrite <- H1.
        rewrite <- H2.
        assert (Z.rem u v = u - v * (u ÷ v)); [apply Z.rem_eq; auto | ].
        rewrite H3.
        ring.
      * exists z1. auto.
Qed.

Theorem Euclid_divide: forall x y u,
  x <> 0 \/ y <> 0 ->
  Euclid (x, y) (u, 0) ->
  (u | x) /\ (u | y).
Proof.
  intros.
  assert ((u | u) /\ (u | 0)). {
    split.
    Search (_ | _).
    apply Z.divide_refl.
    Search (_ | 0).
    apply Z.divide_0_r.
  }
  apply (Euclid_invariant1 x y u 0 u).
  auto.
  auto.
Qed.

Lemma Euclid_invariant2: forall x y u v d,
  Euclid (x, y) (u, v) ->
  (d | x) /\ (d | y) ->
  (d | u) /\ (d | v).
Proof.
  intros x y u v d H1 H2.
  remember (x, y) as xy eqn: Hxy.
  remember (u, v) as uv eqn: Huv.
  revert x y u v d H2 Hxy Huv.
  induction H1; intros;
  inversion Hxy; inversion Huv;
  try (subst u0 v0);
  try (subst x0 y0);
  clear Hxy Huv.
  - subst u v. apply H2.
  - clear H1.
    specialize IHEuclid with (x0 := x) (y0 := y) (u0 := u) (v0 := v) (d := d).
    apply IHEuclid in H2; auto.
    destruct H2 as [?H ?H].
    unfold Z.divide in *.
    destruct H1 as [z2 H2].
    destruct H0 as [z1 H1].
    split.
    + exists z2. auto.
    + clear IHEuclid.
      rewrite Z.rem_eq; auto.
      exists (z1 - u ÷ v * z2).
      Search ((_ - _) * _).
      rewrite Z.mul_sub_distr_r.
      rewrite <- H1.
      Search (_ * _ * _).
      rewrite <- Z.mul_assoc.
      rewrite <- H2.
      ring.
Qed.

Lemma abs_notzero_ge_1: forall x: Z,
  x <> 0 -> 1 <= Z.abs x.
Proof.
  intros.
  destruct (Z.abs x) eqn: Hx.
  - unfold not in H. exfalso.
    Search (Z.abs _ = 0).
    apply (Z.abs_0_iff x) in Hx. auto.
  - Search (_ < _ -> _ <= _).
    replace 1 with (Z.succ 0).
    apply Zlt_le_succ.
    apply Z.gt_lt.
    apply Zgt_pos_0.
    auto.
  - assert (Z.neg p >= 0). {
      rewrite <- Hx.
      Search(_ <= _ -> _ >= _).
      apply Z.le_ge.
      apply Z.abs_nonneg.
    }
    assert (Z.neg p < 0). { apply Zlt_neg_0. }
    apply H0 in H1. exfalso. auto.
Qed.

Lemma mul_notzero: forall x y z,
  x = y * z -> x <> 0 -> y <> 0.
Proof.
  intros.
  destruct y.
  - simpl in H. rewrite H in H0. apply H0.
  - unfold not. intros.
    assert (Z.pos p > 0). { apply Zgt_pos_0. }
    rewrite H1 in H2. inversion H2.
  - unfold not. intros.
    assert (Z.neg p < 0). { apply Zlt_neg_0. }
    rewrite H1 in H2. inversion H2.
Qed.

Lemma Euclid_notzero: forall x y u,
  x <> 0 \/ y <> 0 ->
  Euclid (x, y) (u, 0) ->
  u <> 0.
Proof.
  intros.
  destruct u.
  - inversion H0.
    + destruct H as [H | H]; try rewrite H4 in H; try rewrite H5 in H; apply H.
    + rewrite H5 in H6. unfold not in H6. exfalso. auto.
  - unfold not. intros.
    assert (Z.pos p > 0). { apply Zgt_pos_0. }
    rewrite H1 in H2. inversion H2.
  - unfold not. intros.
    assert (Z.neg p < 0). { apply Zlt_neg_0. }
    rewrite H1 in H2. inversion H2.
Qed.

Theorem Euclid_greatest: forall x y u u',
  x <> 0 \/ y <> 0 ->
  Euclid (x, y) (u, 0) ->
  (u' | x) /\ (u' | y) ->
  Z.abs u' <= Z.abs u.
Proof.
  intros.
  assert (I: (u' | u) /\ (u' | 0)). 
    apply Euclid_invariant2 with (x := x) (y := y); auto.
  assert (J: (u | x) /\ (u | y)).
    apply Euclid_divide; auto.
  destruct I as [I _].
  destruct J as [J1 J2].
  destruct I as [zI I].
  destruct J1 as [zJ1 J1].
  destruct J2 as [zJ2 J2].
  rewrite I.
  Search Z.abs.
  rewrite Z.abs_mul.
  assert (K: zI <> 0). {
    assert (u <> 0). apply (Euclid_notzero x y u); auto.
    apply (mul_notzero u zI u'); auto.
  }
  destruct u' eqn: Hu.
  - rewrite Z.mul_0_r. simpl. omega.
  - assert (H': Z.abs (Z.pos p) = Z.pos p) by auto; rewrite H'; clear H'. 
    Search (_ * _ <= _ * _).
    assert (H': 1 * Z.pos p <= Z.abs zI * Z.pos p -> Z.pos p <= Z.abs zI * Z.pos p) by auto; apply H'; clear H'.
    apply (Zmult_gt_0_le_compat_r 1 (Z.abs zI) (Z.pos p)).
    Search (Z.pos _ > 0).
    apply Zgt_pos_0.
    apply abs_notzero_ge_1; auto.
  - assert (H': Z.abs (Z.neg p) = Z.pos p) by auto; rewrite H'; clear H'. 
    Search (_ * _ <= _ * _).
    assert (H': 1 * Z.pos p <= Z.abs zI * Z.pos p -> Z.pos p <= Z.abs zI * Z.pos p) by auto; apply H'; clear H'.
    apply (Zmult_gt_0_le_compat_r 1 (Z.abs zI) (Z.pos p)).
    Search (Z.pos _ > 0).
    apply Zgt_pos_0.
    apply abs_notzero_ge_1; auto.
Qed.

Inductive Euclid_count: Z * Z -> Z * Z -> Z -> Prop :=
| Euclid_count_refl: forall x y, Euclid_count (x, y) (x, y) 0
| Euclid_count_step: forall x y u v n,
                            Euclid_count (x, y) (u, v) n ->
                            v <> 0 ->
                            Euclid_count (x, y) (v, Z.rem u v) (n + 1).

Lemma Euclid_count_nonneg: forall x y u v n,
  Euclid_count (x, y) (u, v) n -> 0 <= n.
Proof.
  intros.
  induction H; omega.
Qed.

Lemma Euclid_beq_still: forall x y u v n,
  Euclid_count (x, y) (u, v) n -> Z.abs x >= Z.abs y -> Z.abs u >= Z.abs v.
Proof.
  intros.
  remember (x, y) as xy eqn: Hxy.
  remember (u, v) as uv eqn: Huv.
  revert u v Huv.
  induction H.
  - intros. inversion Hxy. inversion Huv. subst x0 y0 u v. auto.
  - inversion Hxy. subst x0 y0. clear Hxy.
    intros. inversion Huv. subst u0 v0. clear Huv.
    assert (Z.abs (Z.rem u v) < Z.abs v); [ apply Z.rem_bound_abs; auto | omega].
Qed.

Lemma Euclid_half_descending: forall u v,
  v <> 0 -> Z.abs u >= Z.abs v -> 2 * Z.abs (Z.rem u v) <= Z.abs u.
Proof.
  intros.
  assert ({2 * Z.abs v <= Z.abs u} + {2 * Z.abs v > Z.abs u});
    [ apply Z_le_gt_dec | ].
  destruct H1 as [H1 | H2].
  - assert (Z.abs (Z.rem u v) <= Z.abs v);
      [ | apply Z.le_trans with (m := 2 * Z.abs v); omega].
    assert (Z.abs (Z.rem u v) < Z.abs v); [ apply Z.rem_bound_abs | apply Z.lt_le_incl]; auto.
  - rewrite <- Z.rem_abs; [ | auto].
    assert (Z.rem (Z.abs u) (Z.abs v) = (Z.abs u) - (Z.abs v) * ((Z.abs u) ÷ (Z.abs v))); [ apply Z.rem_eq; omega | ].
    rewrite H1; clear H1.
    Search (_ * (_ - _)).
    rewrite Z.mul_sub_distr_l.
    assert (Z.abs u <= 2 * (Z.abs v * (Z.abs u ÷ Z.abs v))); [ | omega].
    assert (1 <= Z.abs u ÷ Z.abs v). {
      replace 1 with (Z.abs v ÷ Z.abs v); [ | apply Z.quot_same; omega].
      apply Z.quot_le_mono; omega.
    }
    apply Z.le_trans with (m := 2 * (Z.abs v * 1)); [omega | ].
    apply Zmult_le_compat_l; [ | omega].
    apply Zmult_le_compat_l; omega.
Qed.

Lemma Euclid_count_log_strong: forall x y u v n, Z.abs x >= Z.abs y ->
  Euclid_count (x, y) (u, v) n ->
  (2 ^ (n / 2) * Z.abs u <= Z.abs x /\ 2 ^ ((n + 1) / 2) * Z.abs v <= Z.abs x).
Proof.
  intros.
  remember (x, y) as xy eqn: Hxy.
  remember (u, v) as uv eqn: Huv.
  revert u v Huv.
  induction H0.
  - intros.
    inversion Hxy.
    inversion Huv.
    subst x0 y0 u v.
    split;
      [replace (2 ^ (0 / 2)) with 1; [rewrite Z.mul_1_l; apply Z.le_refl | auto] | 
       replace (2 ^ ((0 + 1) / 2)) with 1; [rewrite Z.mul_1_l; omega | auto]].
  - intros.
    inversion Huv. 
    inversion Hxy. 
    subst u0 v0 x0 y0.
    specialize IHEuclid_count with (u0 := u) (v0 := v).
    apply IHEuclid_count in Hxy; auto.
    clear Huv IHEuclid_count.
    split; [tauto | ].
    replace (n + 1 + 1) with (n + 1 * 2); [ | omega].
    rewrite Z.div_add; [ | omega].
    assert (POS: 0 <= n). apply (Euclid_count_nonneg x y u v n); auto.
    rewrite Z.pow_add_r; [ | apply Z.div_pos; [auto | omega] | omega].
    simpl.
    replace (Z.pow_pos 2 1) with 2; [ | auto].
    assert (2 * Z.abs (Z.rem u v) <= Z.abs u).
    + apply Euclid_half_descending; [auto | apply (Euclid_beq_still x y u v n); auto].
    + apply Z.le_trans with (m := 2 ^ (n / 2) * Z.abs u); [ | tauto].
      rewrite Zmult_assoc_reverse.
      apply Zmult_le_compat_l with (p := 2 ^ (n / 2)); [auto | apply Z.pow_nonneg; omega].
Qed.

Lemma Euclid_count_notzero: forall x y u n,
  x <> 0 \/ y <> 0 ->
  Euclid_count (x, y) (u, 0) n ->
  u <> 0.
Proof.
  intros.
  destruct u.
  - inversion H0.
    + destruct H as [H | H]; try rewrite H4 in H; try rewrite H5 in H; apply H.
    + rewrite H5 in H6. unfold not in H6. exfalso. auto.
  - unfold not. intros.
    assert (Z.pos p > 0). { apply Zgt_pos_0. }
    rewrite H1 in H2. inversion H2.
  - unfold not. intros.
    assert (Z.neg p < 0). { apply Zlt_neg_0. }
    rewrite H1 in H2. inversion H2.
Qed.

Lemma Euclid_count_log_ge: forall x y u n,
  x <> 0 \/ y <> 0 ->
  Z.abs x >= Z.abs y ->
  Euclid_count (x, y) (u, 0) n ->
  2 ^ (n / 2) <= Z.abs x + Z.abs y.
Proof.
  intros.
  assert (Z.abs x >= Z.abs y). omega.
  assert (2 ^ (n / 2) * Z.abs u <= Z.abs x /\ 2 ^ ((n + 1) / 2) * Z.abs 0 <= Z.abs x);
    [apply (Euclid_count_log_strong x y u 0 n); auto | ].
  assert (u <> 0); [apply (Euclid_count_notzero x y u n); auto | ].
  assert (1 <= Z.abs u); [apply abs_notzero_ge_1; auto | ].
  assert (0 <= Z.abs y); [apply Z.abs_nonneg | ].
  replace (2 ^ (n / 2)) with (2 ^ (n / 2) * 1); [ | omega].
  apply Z.le_trans with (m := 2 ^ (n / 2) * Z.abs u);
    [apply Zmult_le_compat_l; [auto | apply Z.pow_nonneg; omega] | ].
  apply Z.le_trans with (m := Z.abs x + 0); [omega | ].
  apply Z.add_le_mono; omega.
Qed.

Lemma Euclid_count_log_lt_step: forall (x y u v n: Z),  
  y <> 0 -> Euclid_count (x, y) (u, v) (n + 1) -> n >= 0 ->
  Euclid_count (y, Z.rem x y) (u, v) n.
Proof.
  intros x y u v n Hy0 H Hn0.
  remember (x, y) as xy eqn: Hxy.
  remember (u, v) as uv eqn: Huv.
  remember (n + 1) as n_1 eqn: Hn1.
  revert u v n Huv Hn1 Hy0 Hn0.
  induction H; [intros; omega | ].
  intros. specialize (IHEuclid_count Hxy u v (n - 1)).
  assert (n = n0); [omega | ].
  subst n0. inversion Hxy. inversion Huv. 
  subst x0 y0 u0 v0. clear Hxy Hn1 Huv.
  assert (I: {n = 1} + {n <> 1}); [apply Z.eq_dec | ].
  destruct I.
  - subst n. clear Hn0 IHEuclid_count.
    inversion H.
    assert (n = 0); [omega | ].
    subst. clear H6.
    inversion H4; subst.
    + constructor; [constructor | auto].
    + assert (0 <= n); [apply (Euclid_count_nonneg x y u1 u0); auto | omega].
  - assert (J: {n = 0} + {n <> 0}); [apply Z.eq_dec | ]. 
    destruct J.
    + subst. clear n0 Hn0 IHEuclid_count.
      inversion H; [constructor | ].
      assert (0 <= n); [apply (Euclid_count_nonneg x y u0 u); auto | omega].
    + assert (0 <= n); [apply (Euclid_count_nonneg x y u v); auto | ].
      assert (Euclid_count (y, Z.rem x y) (u, v) (n - 1)); [apply IHEuclid_count; auto; omega | ].
      replace n with (n - 1 + 1); [ | omega].
      constructor; auto.
Qed.

Lemma Euclid_count_log_lt: forall x y u n,
  x <> 0 \/ y <> 0 ->
  Z.abs x < Z.abs y ->
  Euclid_count (x, y) (u, 0) n ->
  2 ^ ((n - 1) / 2) <= Z.abs x + Z.abs y.
Proof.
  intros.
  assert (y <> 0). {
    destruct H as [H | H]; [ | auto].
    assert (K: {y = 0} + {y <> 0}); [apply Z.eq_dec | ].
    destruct K; [subst | auto].
    assert (0 <= Z.abs x); [apply Z.abs_nonneg | ].
    replace (Z.abs 0) with 0 in H0; [omega | auto].
  } 
  assert (Euclid_count (y, Z.rem x y) (u, 0) (n - 1)). {
    apply Euclid_count_log_lt_step.
    auto. 
    replace (n - 1 + 1) with n; [auto | omega].
    assert (0 <= n); [apply (Euclid_count_nonneg x y u 0); auto | ].
    assert (J: {n = 0} + {n <> 0}); [apply Z.eq_dec | ].
    destruct J; [ | omega].
    inversion H1; [subst; unfold not in H; exfalso; auto | subst].
    assert (0 <= n0); [apply (Euclid_count_nonneg x y u0 u n0); auto | omega].
  }
  assert (2 ^ ((n - 1) / 2) <= Z.abs y + Z.abs (Z.rem x y)). { 
    apply (Euclid_count_log_ge y (Z.rem x y) u (n - 1)); auto.
    assert (Z.abs (Z.rem x y) < Z.abs y); [apply Z.rem_bound_abs; auto | omega].
  }
  assert(Z.rem x y = x); [apply Z.rem_small_iff; auto | ].
  rewrite H5 in H4.
  omega.
Qed.

Theorem Euclid_count_log: forall x y u n,
  x <> 0 \/ y <> 0 ->
  Euclid_count (x, y) (u, 0) n ->
  2 ^ ((n - 1) / 2) <= Z.abs x + Z.abs y.
Proof.
  intros.
  assert (Hde: {Z.abs x < Z.abs y} + {Z.abs x >= Z.abs y});
    [ apply Z_lt_ge_dec | ].
  destruct Hde as [H1 | H2].
  - apply (Euclid_count_log_lt x y u n); auto. 
  - apply Z.le_trans with (m := 2 ^ (n / 2)); [ | apply (Euclid_count_log_ge x y u n); auto].
    apply Z.pow_le_mono_r; [omega | ].
    apply Z.div_le_mono; omega.
Qed.

