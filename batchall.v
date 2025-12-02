(******************************************************************************)
(*                                                                            *)
(*        Clan Batchall: Formal Verification of Ritual Combat Protocol        *)
(*                                                                            *)
(*        Machine-checked formalization of the Clan challenge system          *)
(*        from BattleTech: batchall ritual, force bidding, honor accounting   *)
(*        as a verified state machine with well-foundedness guarantees.       *)
(*                                                                            *)
(*        "I am Star Colonel Timur Malthus, Clan Jade Falcon.                 *)
(*         We claim this enclave. With what do you defend?"                   *)
(*                                                                            *)
(*        "Star Captain Dwillt Radick, Clan Wolf. One Trinary."               *)
(*                                                                            *)
(*        "Aff. I bid one Binary."                                            *)
(*                                                                            *)
(*        "Bargained well and done."                                          *)
(*                                                                            *)
(*        Author: Charles C. Norton                                           *)
(*        Date: December 2, 2025                                              *)
(*                                                                            *)
(******************************************************************************)

(** * Section 1: Imports and Foundational Setup *)

From Coq Require Import List.
From Coq Require Import Arith.
From Coq Require Import PeanoNat.
From Coq Require Import Bool.
From Coq Require Import Relations.
From Coq Require Import Wellfounded.
From Coq Require Import Lia.
From Coq Require Import ZArith.

Import ListNotations.
Open Scope nat_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Section 2: Clans *)

Inductive Clan : Type :=
  | ClanWolf
  | ClanJadeFalcon
  | ClanSmokeJaguar
  | ClanGhostBear
  | ClanNovaCat
  | ClanDiamondShark
  | ClanSteelViper
  | ClanHellsHorses
  | ClanCoyote
  | ClanStarAdder
  | ClanBloodSpirit
  | ClanFireMandrill
  | ClanCloudCobra
  | ClanSnowRaven
  | ClanGoliathScorpion
  | ClanIceHellion
  | ClanGeneric (id : nat).

Definition clan_eq_dec : forall (c1 c2 : Clan), {c1 = c2} + {c1 <> c2}.
Proof.
  decide equality.
  apply Nat.eq_dec.
Defined.

Definition clan_eqb (c1 c2 : Clan) : bool :=
  if clan_eq_dec c1 c2 then true else false.

Lemma clan_eqb_eq : forall c1 c2, clan_eqb c1 c2 = true <-> c1 = c2.
Proof.
  intros c1 c2. unfold clan_eqb.
  destruct (clan_eq_dec c1 c2); split; intros; auto; discriminate.
Qed.

Lemma clan_eqb_refl : forall c, clan_eqb c c = true.
Proof.
  intros c. apply clan_eqb_eq. reflexivity.
Qed.

(** * Section 3: Ranks and Commanders *)

Inductive Rank : Type :=
  | Warrior
  | PointCommander
  | StarCommander
  | StarCaptain
  | StarColonel
  | GalaxyCommander
  | Khan
  | SaKhan
  | Loremaster.

Definition rank_to_nat (r : Rank) : nat :=
  match r with
  | Warrior => 0
  | PointCommander => 1
  | StarCommander => 2
  | StarCaptain => 3
  | StarColonel => 4
  | GalaxyCommander => 5
  | Khan => 6
  | SaKhan => 7
  | Loremaster => 8
  end.

Definition rank_le (r1 r2 : Rank) : bool :=
  rank_to_nat r1 <=? rank_to_nat r2.

Record Commander : Type := mkCommander {
  comm_id : nat;
  comm_clan : Clan;
  comm_rank : Rank;
  comm_bloodnamed : bool
}.

Definition commander_eq_dec : forall (c1 c2 : Commander), {c1 = c2} + {c1 <> c2}.
Proof.
  decide equality.
  - apply Bool.bool_dec.
  - decide equality.
  - apply clan_eq_dec.
  - apply Nat.eq_dec.
Defined.

(** * Section 4: Unit Types and Combat Units *)

Inductive UnitClass : Type :=
  | OmniMech
  | BattleMech
  | ProtoMech
  | Aerospace
  | OmniFighter
  | Vehicle
  | BattleArmor
  | Elemental
  | Infantry.

Inductive WeightClass : Type :=
  | Ultralight
  | Light
  | Medium
  | Heavy
  | Assault
  | SuperHeavy.

Definition weight_to_nat (w : WeightClass) : nat :=
  match w with
  | Ultralight => 0
  | Light => 1
  | Medium => 2
  | Heavy => 3
  | Assault => 4
  | SuperHeavy => 5
  end.

Record Unit : Type := mkUnit {
  unit_id : nat;
  unit_class : UnitClass;
  unit_weight : WeightClass;
  unit_tonnage : nat;
  unit_skill : nat;
  unit_is_elite : bool;
  unit_is_clan : bool
}.

(** * Section 5: Forces and Force Metrics *)

Definition Force : Type := list Unit.

Record ForceMetrics : Type := mkForceMetrics {
  fm_count : nat;
  fm_tonnage : nat;
  fm_elite_count : nat;
  fm_clan_count : nat
}.

Definition empty_metrics : ForceMetrics :=
  mkForceMetrics 0 0 0 0.

Definition unit_to_metrics (u : Unit) : ForceMetrics :=
  mkForceMetrics
    1
    (unit_tonnage u)
    (if unit_is_elite u then 1 else 0)
    (if unit_is_clan u then 1 else 0).

Definition metrics_add (m1 m2 : ForceMetrics) : ForceMetrics :=
  mkForceMetrics
    (fm_count m1 + fm_count m2)
    (fm_tonnage m1 + fm_tonnage m2)
    (fm_elite_count m1 + fm_elite_count m2)
    (fm_clan_count m1 + fm_clan_count m2).

Definition force_metrics (f : Force) : ForceMetrics :=
  fold_right (fun u acc => metrics_add (unit_to_metrics u) acc) empty_metrics f.

Lemma force_metrics_nil : force_metrics [] = empty_metrics.
Proof. reflexivity. Qed.

Lemma force_metrics_cons : forall u f,
  force_metrics (u :: f) = metrics_add (unit_to_metrics u) (force_metrics f).
Proof. reflexivity. Qed.

(** * Section 6: Force Comparison - Partial Order *)

Definition fm_le (m1 m2 : ForceMetrics) : Prop :=
  fm_count m1 <= fm_count m2 /\
  fm_tonnage m1 <= fm_tonnage m2 /\
  fm_elite_count m1 <= fm_elite_count m2 /\
  fm_clan_count m1 <= fm_clan_count m2.

Definition fm_lt (m1 m2 : ForceMetrics) : Prop :=
  fm_le m1 m2 /\ m1 <> m2.

Definition fm_le_dec (m1 m2 : ForceMetrics) : {fm_le m1 m2} + {~ fm_le m1 m2}.
Proof.
  unfold fm_le.
  destruct (le_dec (fm_count m1) (fm_count m2));
  destruct (le_dec (fm_tonnage m1) (fm_tonnage m2));
  destruct (le_dec (fm_elite_count m1) (fm_elite_count m2));
  destruct (le_dec (fm_clan_count m1) (fm_clan_count m2));
  try (left; auto; fail);
  right; intros [H1 [H2 [H3 H4]]]; contradiction.
Defined.

Lemma fm_le_refl : forall m, fm_le m m.
Proof.
  intros m. unfold fm_le. auto.
Qed.

Lemma fm_le_trans : forall m1 m2 m3,
  fm_le m1 m2 -> fm_le m2 m3 -> fm_le m1 m3.
Proof.
  intros m1 m2 m3 [H1a [H1b H1c]] [H2a [H2b H2c]].
  unfold fm_le. repeat split; lia.
Qed.

Lemma fm_le_antisym : forall m1 m2,
  fm_le m1 m2 -> fm_le m2 m1 -> m1 = m2.
Proof.
  intros [c1 t1 e1 l1] [c2 t2 e2 l2].
  unfold fm_le. simpl.
  intros [H1a [H1b H1c]] [H2a [H2b H2c]].
  assert (c1 = c2) by lia.
  assert (t1 = t2) by lia.
  assert (e1 = e2) by lia.
  subst. f_equal. lia.
Qed.

Definition force_le (f1 f2 : Force) : Prop :=
  fm_le (force_metrics f1) (force_metrics f2).

Definition force_lt (f1 f2 : Force) : Prop :=
  fm_lt (force_metrics f1) (force_metrics f2).

(** * Section 7: Well-Founded Order on Force Metrics *)

Definition fm_measure (m : ForceMetrics) : nat :=
  fm_count m + fm_tonnage m + fm_elite_count m + fm_clan_count m.

Lemma fm_lt_measure_decreasing : forall m1 m2,
  fm_lt m1 m2 -> fm_measure m1 < fm_measure m2 \/
                 (fm_measure m1 = fm_measure m2 /\ m1 <> m2 /\ fm_le m1 m2).
Proof.
  intros m1 m2 [Hle Hneq].
  unfold fm_le in Hle. unfold fm_measure.
  destruct Hle as [H1 [H2 [H3 H4]]].
  destruct (Nat.eq_dec (fm_count m1 + fm_tonnage m1 + fm_elite_count m1 + fm_clan_count m1)
                       (fm_count m2 + fm_tonnage m2 + fm_elite_count m2 + fm_clan_count m2)).
  - right. split; auto. split; auto. unfold fm_le. auto.
  - left. lia.
Qed.

Definition fm_lt_wf_rel (m1 m2 : ForceMetrics) : Prop :=
  fm_measure m1 < fm_measure m2.

Lemma fm_lt_wf_rel_wf : well_founded fm_lt_wf_rel.
Proof.
  unfold fm_lt_wf_rel.
  apply well_founded_ltof.
Qed.

(** * Section 8: Stakes and Locations *)

Inductive TrialType : Type :=
  | TrialOfPosition
  | TrialOfPossession
  | TrialOfRefusal
  | TrialOfGrievance
  | TrialOfBloodright
  | TrialOfAbjuration
  | TrialOfAnnihilation.

Definition trial_type_eq_dec : forall (t1 t2 : TrialType), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

Definition trial_severity (t : TrialType) : nat :=
  match t with
  | TrialOfPosition => 1
  | TrialOfPossession => 2
  | TrialOfRefusal => 2
  | TrialOfGrievance => 1
  | TrialOfBloodright => 3
  | TrialOfAbjuration => 4
  | TrialOfAnnihilation => 5
  end.

Definition trial_requires_circle_of_equals (t : TrialType) : bool :=
  match t with
  | TrialOfBloodright => true
  | TrialOfAnnihilation => true
  | _ => false
  end.

Definition trial_is_lethal (t : TrialType) : bool :=
  match t with
  | TrialOfAnnihilation => true
  | _ => false
  end.

Lemma trial_severity_positive : forall t,
  trial_severity t >= 1.
Proof.
  intros t. destruct t; simpl; lia.
Qed.

Lemma annihilation_most_severe : forall t,
  trial_severity t <= trial_severity TrialOfAnnihilation.
Proof.
  intros t. destruct t; simpl; lia.
Qed.

Inductive Prize : Type :=
  | PrizeWorld (world_id : nat)
  | PrizeEnclave (enclave_id : nat)
  | PrizeFacility (facility_id : nat)
  | PrizeBloodright (bloodname : nat)
  | PrizeHonor
  | PrizeTrial (trial : TrialType).

Inductive Location : Type :=
  | LocPlanetSurface (world_id : nat) (region_id : nat)
  | LocOrbital (world_id : nat)
  | LocDeepSpace (sector_id : nat)
  | LocEnclave (enclave_id : nat).

Record Stakes : Type := mkStakes {
  stakes_attacker_prize : Prize;
  stakes_defender_prize : option Prize;
  stakes_hegira_allowed : bool
}.

(** * Section 8b: Zellbrigen - The Honor Code of Single Combat *)

Inductive ZellbrigenStatus : Type :=
  | ZellActive
  | ZellBroken (violator : nat)
  | ZellSuspended
  | ZellNotApplicable.

Record ZellbrigenRules : Type := mkZellbrigenRules {
  zell_one_on_one : bool;
  zell_no_physical_attacks : bool;
  zell_declare_targets : bool;
  zell_respect_ejections : bool
}.

Definition strict_zellbrigen : ZellbrigenRules :=
  mkZellbrigenRules true true true true.

Definition relaxed_zellbrigen : ZellbrigenRules :=
  mkZellbrigenRules true false false true.

Inductive ZellbrigenViolation : Type :=
  | ViolGangUp
  | ViolPhysicalAttack
  | ViolUndeclaredTarget
  | ViolAttackEjected
  | ViolOther (code : nat).

Definition zell_violation_severity (v : ZellbrigenViolation) : nat :=
  match v with
  | ViolGangUp => 3
  | ViolPhysicalAttack => 1
  | ViolUndeclaredTarget => 2
  | ViolAttackEjected => 5
  | ViolOther _ => 1
  end.

Lemma zell_violation_severity_positive : forall v,
  zell_violation_severity v >= 1.
Proof.
  intros v. destruct v; simpl; lia.
Qed.

(** * Section 8c: Safcon - Safe Conduct Protocol *)

Inductive SafconStatus : Type :=
  | SafconGranted
  | SafconDenied
  | SafconViolated (by_side : nat)
  | SafconExpired
  | SafconNotRequested.

Record SafconTerms : Type := mkSafconTerms {
  safcon_granted : bool;
  safcon_jumpship_protected : bool;
  safcon_dropship_protected : bool;
  safcon_duration_hours : nat;
  safcon_granting_clan : Clan
}.

Definition default_safcon (grantor : Clan) : SafconTerms :=
  mkSafconTerms true true true 72 grantor.

Definition safcon_active (s : SafconTerms) : bool :=
  safcon_granted s && negb (Nat.eqb (safcon_duration_hours s) 0).

Lemma safcon_default_active : forall c,
  safcon_active (default_safcon c) = true.
Proof.
  intros c. unfold safcon_active, default_safcon. simpl. reflexivity.
Qed.

Inductive SafconViolationType : Type :=
  | SafconAttackJumpship
  | SafconAttackDropship
  | SafconAttackInTransit
  | SafconDenyLanding.

Definition safcon_violation_dishonor (v : SafconViolationType) : nat :=
  match v with
  | SafconAttackJumpship => 10
  | SafconAttackDropship => 5
  | SafconAttackInTransit => 8
  | SafconDenyLanding => 3
  end.

Lemma safcon_violation_always_dishonorable : forall v,
  safcon_violation_dishonor v >= 3.
Proof.
  intros v. destruct v; simpl; lia.
Qed.

(** * Section 9: Bids *)

Inductive Side : Type := Attacker | Defender.

Definition side_eq_dec : forall (s1 s2 : Side), {s1 = s2} + {s1 <> s2}.
Proof. decide equality. Defined.

Definition side_eqb (s1 s2 : Side) : bool :=
  match s1, s2 with
  | Attacker, Attacker => true
  | Defender, Defender => true
  | _, _ => false
  end.

Record ForceBid : Type := mkForceBid {
  bid_side : Side;
  bid_force : Force;
  bid_commander : Commander
}.

Definition bid_metrics (b : ForceBid) : ForceMetrics :=
  force_metrics (bid_force b).

Definition bid_lt (b1 b2 : ForceBid) : Prop :=
  bid_side b1 = bid_side b2 /\
  fm_lt (bid_metrics b1) (bid_metrics b2).

(** * Section 10: Batchall Protocol Messages *)

Record BatchallChallenge : Type := mkBatchallChallenge {
  bc_challenger : Commander;
  bc_prize : Prize;
  bc_initial_force : Force
}.

Record BatchallResponse : Type := mkBatchallResponse {
  br_defender : Commander;
  br_location : Location;
  br_defender_force : Force;
  br_counter_stakes : option Stakes
}.

Inductive RefusalReason : Type :=
  | RefusalDishonorableConduct
  | RefusalNoJurisdiction
  | RefusalInvalidChallenger
  | RefusalAlreadyContested
  | RefusalOther (code : nat).

(** * Section 11: Protocol Actions *)

Inductive ProtocolAction : Type :=
  | ActChallenge (challenge : BatchallChallenge)
  | ActRespond (response : BatchallResponse)
  | ActRefuse (reason : RefusalReason)
  | ActBid (bid : ForceBid)
  | ActPass (side : Side)
  | ActClose
  | ActBreakBid
  | ActWithdraw (side : Side).

(** * Section 12: Batchall Protocol State Machine *)

Inductive ReadyStatus : Type :=
  | NeitherReady
  | AttackerReady
  | DefenderReady
  | BothReady.

Inductive BatchallPhase : Type :=
  | PhaseIdle
  | PhaseChallenged (challenge : BatchallChallenge)
  | PhaseResponded (challenge : BatchallChallenge) (response : BatchallResponse)
  | PhaseBidding (challenge : BatchallChallenge)
                 (response : BatchallResponse)
                 (attacker_bid : ForceBid)
                 (defender_bid : ForceBid)
                 (bid_history : list ForceBid)
                 (ready : ReadyStatus)
  | PhaseRefused (challenge : BatchallChallenge) (reason : RefusalReason)
  | PhaseAgreed (challenge : BatchallChallenge)
                (response : BatchallResponse)
                (final_attacker_bid : ForceBid)
                (final_defender_bid : ForceBid)
  | PhaseAborted.

(** * Section 13: Protocol Transition Rules *)

Inductive BatchallStep : BatchallPhase -> ProtocolAction -> BatchallPhase -> Prop :=

  | StepChallenge : forall chal,
      BatchallStep PhaseIdle (ActChallenge chal) (PhaseChallenged chal)

  | StepRefuse : forall chal reason,
      BatchallStep (PhaseChallenged chal) (ActRefuse reason) (PhaseRefused chal reason)

  | StepRespond : forall chal resp,
      BatchallStep (PhaseChallenged chal) (ActRespond resp) (PhaseResponded chal resp)

  | StepStartBidding : forall chal resp,
      let atk_bid := mkForceBid Attacker (bc_initial_force chal) (bc_challenger chal) in
      let def_bid := mkForceBid Defender (br_defender_force resp) (br_defender resp) in
      BatchallStep (PhaseResponded chal resp)
                   (ActBid atk_bid)
                   (PhaseBidding chal resp atk_bid def_bid [] NeitherReady)

  | StepAttackerBid : forall chal resp atk_bid def_bid hist ready new_bid,
      bid_side new_bid = Attacker ->
      fm_lt (bid_metrics new_bid) (bid_metrics atk_bid) ->
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist ready)
                   (ActBid new_bid)
                   (PhaseBidding chal resp new_bid def_bid (atk_bid :: hist) NeitherReady)

  | StepDefenderBid : forall chal resp atk_bid def_bid hist ready new_bid,
      bid_side new_bid = Defender ->
      fm_lt (bid_metrics new_bid) (bid_metrics def_bid) ->
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist ready)
                   (ActBid new_bid)
                   (PhaseBidding chal resp atk_bid new_bid (def_bid :: hist) NeitherReady)

  | StepAttackerPass : forall chal resp atk_bid def_bid hist,
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist NeitherReady)
                   (ActPass Attacker)
                   (PhaseBidding chal resp atk_bid def_bid hist AttackerReady)

  | StepDefenderPass : forall chal resp atk_bid def_bid hist,
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist NeitherReady)
                   (ActPass Defender)
                   (PhaseBidding chal resp atk_bid def_bid hist DefenderReady)

  | StepCloseFromAttackerReady : forall chal resp atk_bid def_bid hist,
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist AttackerReady)
                   (ActPass Defender)
                   (PhaseAgreed chal resp atk_bid def_bid)

  | StepCloseFromDefenderReady : forall chal resp atk_bid def_bid hist,
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist DefenderReady)
                   (ActPass Attacker)
                   (PhaseAgreed chal resp atk_bid def_bid)

  | StepWithdraw : forall chal resp atk_bid def_bid hist ready side,
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist ready)
                   (ActWithdraw side)
                   PhaseAborted.

(** * Section 14: Protocol Traces *)

Inductive BatchallTrace : BatchallPhase -> Type :=
  | TraceNil : forall phase, BatchallTrace phase
  | TraceCons : forall phase1 action phase2,
      BatchallStep phase1 action phase2 ->
      BatchallTrace phase2 ->
      BatchallTrace phase1.

Fixpoint trace_length {phase : BatchallPhase} (t : BatchallTrace phase) : nat :=
  match t with
  | TraceNil _ => 0
  | @TraceCons _ _ _ _ rest => S (trace_length rest)
  end.

(** * Section 15: Bid Sequence Extraction *)

Fixpoint extract_bids_from_history (hist : list ForceBid) (s : Side) : list ForceBid :=
  match hist with
  | [] => []
  | b :: rest =>
      if side_eqb (bid_side b) s
      then b :: extract_bids_from_history rest s
      else extract_bids_from_history rest s
  end.

(** * Section 16: Strictly Decreasing Bids Property *)

Inductive StrictlyDecreasing : list ForceBid -> Prop :=
  | SDNil : StrictlyDecreasing []
  | SDSingle : forall b, StrictlyDecreasing [b]
  | SDCons : forall b1 b2 rest,
      fm_lt (bid_metrics b1) (bid_metrics b2) ->
      StrictlyDecreasing (b2 :: rest) ->
      StrictlyDecreasing (b1 :: b2 :: rest).

Lemma strictly_decreasing_tail : forall b rest,
  StrictlyDecreasing (b :: rest) -> StrictlyDecreasing rest.
Proof.
  intros b rest H.
  inversion H; subst.
  - constructor.
  - assumption.
Qed.

(** * Section 17: Protocol Invariants *)

Definition valid_bidding_state (chal : BatchallChallenge) (resp : BatchallResponse)
                               (atk_bid def_bid : ForceBid) (hist : list ForceBid) : Prop :=
  bid_side atk_bid = Attacker /\
  bid_side def_bid = Defender /\
  fm_le (bid_metrics atk_bid) (force_metrics (bc_initial_force chal)) /\
  fm_le (bid_metrics def_bid) (force_metrics (br_defender_force resp)).

Lemma step_preserves_bid_validity : forall chal resp atk def hist ready action phase',
  valid_bidding_state chal resp atk def hist ->
  BatchallStep (PhaseBidding chal resp atk def hist ready) action phase' ->
  match phase' with
  | PhaseBidding _ _ atk' def' hist' _ => valid_bidding_state chal resp atk' def' hist'
  | _ => True
  end.
Proof.
  intros chal resp atk def hist ready action phase' Hvalid Hstep.
  inversion Hstep; subst; auto;
  unfold valid_bidding_state in *;
  destruct Hvalid as [Ha [Hd [Hale Hdle]]];
  repeat split; auto;
  unfold fm_lt, fm_le in *;
  try match goal with
  | [ H : _ /\ _ |- _ ] => destruct H as [[? [? [? ?]]] ?]
  end;
  repeat split; lia.
Qed.

(** * Section 18: Termination - No Infinite Bidding *)

Definition bid_measure (b : ForceBid) : nat := fm_measure (bid_metrics b).

Lemma bid_lt_decreases_measure : forall b1 b2,
  fm_lt (bid_metrics b1) (bid_metrics b2) ->
  bid_measure b1 < bid_measure b2 \/ bid_measure b1 = bid_measure b2.
Proof.
  intros b1 b2 [Hle Hneq].
  unfold bid_measure, fm_measure, fm_le in *.
  destruct Hle as [H1 [H2 H3]].
  lia.
Qed.

Lemma fm_lt_wf : well_founded (fun m1 m2 => fm_lt m1 m2).
Proof.
  apply well_founded_lt_compat with (f := fm_measure).
  intros m1 m2 [Hle Hneq].
  unfold fm_measure.
  destruct Hle as [H1 [H2 [H3 H4]]].
  destruct m1 as [c1 t1 e1 l1].
  destruct m2 as [c2 t2 e2 l2].
  simpl in *.
  destruct (Nat.eq_dec (c1 + t1 + e1 + l1) (c2 + t2 + e2 + l2)).
  - exfalso. apply Hneq.
    assert (c1 = c2) by lia.
    assert (t1 = t2) by lia.
    assert (e1 = e2) by lia.
    assert (l1 = l2) by lia.
    subst. reflexivity.
  - lia.
Qed.

Lemma fm_lt_implies_measure_lt : forall m1 m2,
  fm_lt m1 m2 -> fm_measure m1 < fm_measure m2.
Proof.
  intros m1 m2 [[H1 [H2 [H3 H4]]] Hneq].
  unfold fm_measure.
  destruct m1 as [c1 t1 e1 l1].
  destruct m2 as [c2 t2 e2 l2].
  simpl in *.
  destruct (Nat.eq_dec (c1 + t1 + e1 + l1) (c2 + t2 + e2 + l2)).
  - exfalso. apply Hneq.
    assert (c1 = c2) by lia.
    assert (t1 = t2) by lia.
    assert (e1 = e2) by lia.
    assert (l1 = l2) by lia.
    subst. reflexivity.
  - lia.
Qed.

Theorem no_infinite_bidding_sequence : forall (seq : nat -> ForceBid),
  (forall n, fm_lt (bid_metrics (seq (S n))) (bid_metrics (seq n))) ->
  False.
Proof.
  intros seq Hdesc.
  assert (Hmeas: forall n, fm_measure (bid_metrics (seq (S n))) < fm_measure (bid_metrics (seq n))).
  { intros n. apply fm_lt_implies_measure_lt. apply Hdesc. }
  assert (Hinc: forall n, fm_measure (bid_metrics (seq n)) + n <= fm_measure (bid_metrics (seq 0))).
  { induction n.
    - simpl. lia.
    - specialize (Hmeas n). lia. }
  specialize (Hinc (S (fm_measure (bid_metrics (seq 0))))).
  lia.
Qed.

(** * Section 19: Honor System *)

Open Scope Z_scope.

Definition Honor : Type := Z.

Record HonorLedger : Type := mkHonorLedger {
  ledger_honor : Commander -> Honor
}.

Definition refusal_honor_delta (reason : RefusalReason) : Honor :=
  match reason with
  | RefusalDishonorableConduct => 2
  | RefusalNoJurisdiction => 0
  | RefusalInvalidChallenger => 1
  | RefusalAlreadyContested => 0
  | RefusalOther _ => -1
  end.

Lemma refusal_dishonorable_gives_honor :
  refusal_honor_delta RefusalDishonorableConduct = 2%Z.
Proof. reflexivity. Qed.

Lemma refusal_other_loses_honor : forall code,
  refusal_honor_delta (RefusalOther code) = (-1)%Z.
Proof. reflexivity. Qed.

Inductive HegiraAction : Type :=
  | HegiraRequest
  | HegiraGrant
  | HegiraDeny
  | HegiraAccept
  | HegiraViolate.

Definition hegira_honor_delta (h : HegiraAction) : Honor :=
  match h with
  | HegiraRequest => 0
  | HegiraGrant => 3
  | HegiraDeny => -2
  | HegiraAccept => 1
  | HegiraViolate => -15
  end.

Lemma hegira_grant_honorable :
  (hegira_honor_delta HegiraGrant > 0)%Z.
Proof. simpl. lia. Qed.

Lemma hegira_deny_dishonorable :
  (hegira_honor_delta HegiraDeny < 0)%Z.
Proof. simpl. lia. Qed.

Lemma hegira_violate_severely_dishonorable :
  (hegira_honor_delta HegiraViolate <= -10)%Z.
Proof. simpl. lia. Qed.

Definition honor_delta (action : ProtocolAction) (actor : Commander) : Honor :=
  match action with
  | ActChallenge _ => 1
  | ActRespond _ => 1
  | ActRefuse reason => refusal_honor_delta reason
  | ActBid _ => 0
  | ActPass _ => 0
  | ActClose => 1
  | ActBreakBid => -10
  | ActWithdraw _ => -2
  end.

Definition update_honor (ledger : HonorLedger) (actor : Commander) (delta : Honor)
    : HonorLedger :=
  mkHonorLedger (fun c =>
    if Nat.eqb (comm_id c) (comm_id actor)
    then ledger_honor ledger c + delta
    else ledger_honor ledger c).

Definition apply_action_honor (ledger : HonorLedger) (action : ProtocolAction)
    (actor : Commander) : HonorLedger :=
  update_honor ledger actor (honor_delta action actor).

Close Scope Z_scope.

(** * Section 20: Internal Bidding - Within Clan *)

Record SubCommander : Type := mkSubCommander {
  subcmd_id : nat;
  subcmd_commander : Commander
}.

Record InternalCandidate : Type := mkInternalCandidate {
  icand_subcommander : SubCommander;
  icand_force : Force
}.

Definition icand_metrics (c : InternalCandidate) : ForceMetrics :=
  force_metrics (icand_force c).

Definition icand_lt (c1 c2 : InternalCandidate) : Prop :=
  fm_lt (icand_metrics c1) (icand_metrics c2).

Inductive InternalPhase : Type :=
  | IPhaseIdle (candidates : list InternalCandidate)
  | IPhaseBidding (candidates : list InternalCandidate)
                  (current_winner : InternalCandidate)
                  (bid_history : list InternalCandidate)
  | IPhaseComplete (winner : InternalCandidate).

Inductive InternalAction : Type :=
  | IActStart (initial : InternalCandidate)
  | IActUndercut (new_candidate : InternalCandidate)
  | IActConcede.

Inductive InternalStep : InternalPhase -> InternalAction -> InternalPhase -> Prop :=
  | IStepStart : forall cands initial,
      In initial cands ->
      InternalStep (IPhaseIdle cands)
                   (IActStart initial)
                   (IPhaseBidding cands initial [])

  | IStepUndercut : forall cands current hist new_cand,
      icand_lt new_cand current ->
      InternalStep (IPhaseBidding cands current hist)
                   (IActUndercut new_cand)
                   (IPhaseBidding cands new_cand (current :: hist))

  | IStepConcede : forall cands current hist,
      InternalStep (IPhaseBidding cands current hist)
                   IActConcede
                   (IPhaseComplete current).

(** * Section 20b: Concurrent Internal Bidding - Galaxy-Level Cutdowns *)

Record ConcurrentBid : Type := mkConcurrentBid {
  cbid_candidate : InternalCandidate;
  cbid_timestamp : nat;
  cbid_priority : nat
}.

Definition cbid_metrics (cb : ConcurrentBid) : ForceMetrics :=
  icand_metrics (cbid_candidate cb).

Definition cbid_better (cb1 cb2 : ConcurrentBid) : Prop :=
  fm_lt (cbid_metrics cb1) (cbid_metrics cb2) \/
  (cbid_metrics cb1 = cbid_metrics cb2 /\ cbid_priority cb1 < cbid_priority cb2).

Inductive ConcurrentPhase : Type :=
  | CPhaseCollecting (deadline : nat) (bids : list ConcurrentBid)
  | CPhaseResolving (bids : list ConcurrentBid)
  | CPhaseResolved (winner : ConcurrentBid).

Definition find_best_bid (bids : list ConcurrentBid) : option ConcurrentBid :=
  match bids with
  | [] => None
  | b :: rest =>
      Some (fold_left (fun acc cb =>
        if fm_le_dec (cbid_metrics cb) (cbid_metrics acc)
        then (if fm_le_dec (cbid_metrics acc) (cbid_metrics cb)
              then (if cbid_priority cb <? cbid_priority acc then cb else acc)
              else cb)
        else acc) rest b)
  end.

Inductive ConcurrentAction : Type :=
  | CActSubmit (bid : ConcurrentBid)
  | CActDeadline
  | CActResolve.

Inductive ConcurrentStep : ConcurrentPhase -> ConcurrentAction -> ConcurrentPhase -> Prop :=
  | CStepSubmit : forall deadline bids new_bid,
      ConcurrentStep (CPhaseCollecting deadline bids)
                     (CActSubmit new_bid)
                     (CPhaseCollecting deadline (new_bid :: bids))

  | CStepDeadline : forall deadline bids,
      bids <> [] ->
      ConcurrentStep (CPhaseCollecting deadline bids)
                     CActDeadline
                     (CPhaseResolving bids)

  | CStepResolve : forall bids winner,
      find_best_bid bids = Some winner ->
      ConcurrentStep (CPhaseResolving bids)
                     CActResolve
                     (CPhaseResolved winner).

Lemma concurrent_submission_preserves_bids : forall deadline bids new_bid bids',
  ConcurrentStep (CPhaseCollecting deadline bids) (CActSubmit new_bid) (CPhaseCollecting deadline bids') ->
  In new_bid bids'.
Proof.
  intros deadline bids new_bid bids' Hstep.
  inversion Hstep; subst. simpl. left. reflexivity.
Qed.

Lemma find_best_bid_in_list : forall bids winner,
  find_best_bid bids = Some winner ->
  In winner bids.
Proof.
  intros bids winner Hfind.
  destruct bids as [|b rest].
  - simpl in Hfind. discriminate.
  - simpl in Hfind. injection Hfind as Heq.
    revert b Heq. induction rest as [|b' rest' IH]; intros b Heq.
    + simpl in Heq. subst. left. reflexivity.
    + simpl in Heq.
      destruct (fm_le_dec (cbid_metrics b') (cbid_metrics b)).
      * destruct (fm_le_dec (cbid_metrics b) (cbid_metrics b')).
        { destruct (cbid_priority b' <? cbid_priority b) eqn:Hprio.
          - specialize (IH b' Heq). destruct IH; [right; left; auto | right; right; auto].
          - specialize (IH b Heq). destruct IH; [left; auto | right; right; auto]. }
        { specialize (IH b' Heq). destruct IH; [right; left; auto | right; right; auto]. }
      * specialize (IH b Heq). destruct IH; [left; auto | right; right; auto].
Qed.

(** * Section 21: Composite System - External + Internal *)

Record ExternalResult : Type := mkExternalResult {
  ext_challenge : BatchallChallenge;
  ext_response : BatchallResponse;
  ext_attacker_bid : ForceBid;
  ext_defender_bid : ForceBid
}.

Record InternalResult : Type := mkInternalResult {
  int_winner : InternalCandidate
}.

Inductive BattleOutcome : Type :=
  | OutcomeAgreed (external : ExternalResult)
                  (attacker_internal : option InternalResult)
                  (defender_internal : option InternalResult)
  | OutcomeRefused (challenge : BatchallChallenge) (reason : RefusalReason)
  | OutcomeAborted.

Inductive Sublist {A : Type} : list A -> list A -> Prop :=
  | SublistNil : forall l, Sublist [] l
  | SublistSkip : forall x l1 l2, Sublist l1 l2 -> Sublist l1 (x :: l2)
  | SublistTake : forall x l1 l2, Sublist l1 l2 -> Sublist (x :: l1) (x :: l2).

Lemma sublist_nil : forall {A : Type} (l : list A), Sublist l [] -> l = [].
Proof.
  intros A l H. inversion H. reflexivity.
Qed.

Lemma force_metrics_monotone : forall u f,
  fm_le (force_metrics f) (force_metrics (u :: f)).
Proof.
  intros u f. unfold fm_le. simpl.
  unfold metrics_add, unit_to_metrics. simpl.
  repeat split; lia.
Qed.

Lemma force_metrics_nonneg : forall f,
  fm_count (force_metrics f) >= 0 /\
  fm_tonnage (force_metrics f) >= 0 /\
  fm_elite_count (force_metrics f) >= 0 /\
  fm_clan_count (force_metrics f) >= 0.
Proof.
  induction f as [|u rest IH].
  - simpl. repeat split; lia.
  - simpl. unfold metrics_add, unit_to_metrics. simpl.
    destruct IH as [H1 [H2 [H3 H4]]].
    repeat split; lia.
Qed.

Lemma sublist_metrics_le : forall f1 f2,
  Sublist f1 f2 -> fm_le (force_metrics f1) (force_metrics f2).
Proof.
  intros f1 f2 H.
  induction H as [l | x l1 l2 Hsub IH | x l1 l2 Hsub IH].
  - simpl. unfold fm_le.
    destruct (force_metrics l) as [c t e cl] eqn:Heq.
    simpl. repeat split; apply Nat.le_0_l.
  - simpl. unfold fm_le in *. destruct IH as [H1 [H2 [H3 H4]]].
    unfold metrics_add, unit_to_metrics. simpl.
    split; [lia|]. split; [lia|]. split; lia.
  - simpl. unfold fm_le in *. destruct IH as [H1 [H2 [H3 H4]]].
    unfold metrics_add, unit_to_metrics. simpl.
    split; [lia|]. split; [lia|]. split; lia.
Qed.

Definition force_sublist (f1 f2 : Force) : Prop := Sublist f1 f2.

Theorem internal_respects_external : forall ext_res int_res,
  force_sublist (icand_force (int_winner int_res))
                (bid_force (ext_attacker_bid ext_res)) ->
  fm_le (icand_metrics (int_winner int_res))
        (bid_metrics (ext_attacker_bid ext_res)).
Proof.
  intros ext_res int_res Hsub.
  unfold icand_metrics, bid_metrics, force_sublist in *.
  apply sublist_metrics_le. exact Hsub.
Qed.

(** * Section 22: Protocol Soundness *)

Definition is_terminal (phase : BatchallPhase) : Prop :=
  match phase with
  | PhaseAgreed _ _ _ _ => True
  | PhaseRefused _ _ => True
  | PhaseAborted => True
  | _ => False
  end.

Definition is_bidding (phase : BatchallPhase) : Prop :=
  match phase with
  | PhaseBidding _ _ _ _ _ _ => True
  | _ => False
  end.

Lemma terminal_no_step : forall phase action phase',
  is_terminal phase ->
  ~ BatchallStep phase action phase'.
Proof.
  intros phase action phase' Hterm Hstep.
  destruct phase; simpl in Hterm; try contradiction.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep.
Qed.

Theorem protocol_determinism : forall phase action phase1 phase2,
  BatchallStep phase action phase1 ->
  BatchallStep phase action phase2 ->
  phase1 = phase2.
Proof.
  intros phase action phase1 phase2 H1 H2.
  inversion H1; subst; inversion H2; subst; try reflexivity; try discriminate.
  all: try match goal with
  | [ H : _ = _ |- _ ] => injection H; intros; subst; reflexivity
  end.
  all: try congruence.
Qed.

(** * Section 23: Main Theorems *)

Theorem batchall_bid_well_founded :
  well_founded (fun b1 b2 => fm_lt (bid_metrics b1) (bid_metrics b2)).
Proof.
  apply well_founded_lt_compat with (f := bid_measure).
  intros b1 b2 [Hle Hneq].
  unfold bid_measure, fm_measure.
  destruct Hle as [H1 [H2 [H3 H4]]].
  destruct (bid_metrics b1) as [c1 t1 e1 l1].
  destruct (bid_metrics b2) as [c2 t2 e2 l2].
  simpl in *.
  destruct (Nat.eq_dec (c1 + t1 + e1 + l1) (c2 + t2 + e2 + l2)).
  - exfalso. apply Hneq.
    assert (c1 = c2) by lia.
    assert (t1 = t2) by lia.
    assert (e1 = e2) by lia.
    assert (l1 = l2) by lia.
    subst. reflexivity.
  - lia.
Qed.

Definition bidding_state_measure (atk_bid def_bid : ForceBid) (ready : ReadyStatus) : nat :=
  let base := 3 * (bid_measure atk_bid + bid_measure def_bid) in
  match ready with
  | NeitherReady => base + 2
  | AttackerReady => base + 1
  | DefenderReady => base + 1
  | BothReady => base
  end.

Lemma bid_decrease_implies_measure_decrease : forall atk atk' def ready,
  fm_measure (bid_metrics atk') < fm_measure (bid_metrics atk) ->
  bidding_state_measure atk' def NeitherReady < bidding_state_measure atk def ready.
Proof.
  intros atk atk' def ready Hlt.
  unfold bidding_state_measure, bid_measure. destruct ready; lia.
Qed.

Lemma def_bid_decrease_implies_measure_decrease : forall atk def def' ready,
  fm_measure (bid_metrics def') < fm_measure (bid_metrics def) ->
  bidding_state_measure atk def' NeitherReady < bidding_state_measure atk def ready.
Proof.
  intros atk def def' ready Hlt.
  unfold bidding_state_measure, bid_measure. destruct ready; lia.
Qed.

Lemma bidding_step_decreases_or_terminal : forall chal resp atk def hist ready action phase',
  BatchallStep (PhaseBidding chal resp atk def hist ready) action phase' ->
  (exists atk' def' hist' ready',
     phase' = PhaseBidding chal resp atk' def' hist' ready' /\
     bidding_state_measure atk' def' ready' < bidding_state_measure atk def ready) \/
  is_terminal phase'.
Proof.
  intros chal resp atk def hist ready action phase' Hstep.
  inversion Hstep; subst.
  - left. do 4 eexists. split; [reflexivity|].
    apply bid_decrease_implies_measure_decrease.
    apply fm_lt_implies_measure_lt. assumption.
  - left. do 4 eexists. split; [reflexivity|].
    apply def_bid_decrease_implies_measure_decrease.
    apply fm_lt_implies_measure_lt. assumption.
  - left. do 4 eexists. split; [reflexivity|].
    unfold bidding_state_measure. lia.
  - left. do 4 eexists. split; [reflexivity|].
    unfold bidding_state_measure. lia.
  - right. simpl. trivial.
  - right. simpl. trivial.
  - right. simpl. trivial.
Qed.

Theorem bidding_terminates_by_measure : forall (chal : BatchallChallenge) (resp : BatchallResponse)
    (atk def : ForceBid) (hist : list ForceBid) (ready : ReadyStatus),
  Acc (fun m1 m2 => m1 < m2)
      (bidding_state_measure atk def ready).
Proof.
  intros. apply Wf_nat.lt_wf.
Qed.

Corollary protocol_honor_preserved : forall ledger action actor,
  ledger_honor (apply_action_honor ledger action actor) actor =
  (ledger_honor ledger actor + honor_delta action actor)%Z.
Proof.
  intros ledger action actor.
  unfold apply_action_honor, update_honor. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(** * Section 24: Extracted Specification Summary *)

Definition BargainedWellAndDone (outcome : BattleOutcome) : Prop :=
  match outcome with
  | OutcomeAgreed _ _ _ => True
  | _ => False
  end.

Definition HonorableConclusion (outcome : BattleOutcome) : Prop :=
  match outcome with
  | OutcomeAgreed _ _ _ => True
  | OutcomeRefused _ RefusalDishonorableConduct => True
  | _ => False
  end.

Theorem honorable_batchall_possible :
  exists chal resp,
    BatchallStep PhaseIdle (ActChallenge chal) (PhaseChallenged chal) /\
    BatchallStep (PhaseChallenged chal) (ActRespond resp) (PhaseResponded chal resp).
Proof.
  exists (mkBatchallChallenge
            (mkCommander 0 ClanWolf StarColonel true)
            (PrizeEnclave 1)
            []).
  exists (mkBatchallResponse
            (mkCommander 1 ClanJadeFalcon StarCaptain true)
            (LocEnclave 1)
            []
            None).
  split.
  - constructor.
  - constructor.
Qed.

(******************************************************************************)
(*                            END OF FORMALIZATION                            *)
(******************************************************************************)
