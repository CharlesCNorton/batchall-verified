(** * Clan Batchall: Formal Verification of Ritual Combat Protocol

    Machine-checked formalization of the Clan challenge system from BattleTech.
    This development formalizes the batchall ritual, force bidding mechanics,
    and honor accounting as a verified state machine with well-foundedness
    guarantees ensuring all bidding sequences terminate.

    The batchall (from "batch" meaning "to call") is the formal Clan ritual
    of challenge. A Clan warrior issues the batchall to claim a prize, the
    defender responds with their defending force, and both sides then bid
    DOWN their committed forces to demonstrate martial prowess and honor.

      "I am Star Colonel Timur Malthus, Clan Jade Falcon.
       We claim this enclave. With what do you defend?"

      "Star Captain Dwillt Radick, Clan Wolf. One Trinary."

      "Aff. I bid one Binary."

      "Bargained well and done."

    Author: Charles C. Norton
    Date: December 2025
*)

(** ** Table of Contents

    - Part I: Foundational Imports and Setup
    - Part II: Domain Types (Clans, Ranks, Units)
    - Part III: Force Metrics and Ordering
    - Part IV: Trials, Stakes, Honor Codes
    - Part V: Protocol Messages and Actions
    - Part VI: State Machine and Transitions
    - Part VII: Honor Accounting System
    - Part VIII: Internal Clan Bidding
    - Part IX: Termination and Soundness
    - Part X: Main Theorems and Examples
*)

From Coq Require Import List.
From Coq Require Import Arith.
From Coq Require Import PeanoNat.
From Coq Require Import Bool.
From Coq Require Import Relations.
From Coq Require Import Wellfounded.
From Coq Require Import Lia.
From Coq Require Import ZArith.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Part I: Foundational Setup *)

(** We work primarily in nat_scope for force metrics calculations. *)
Open Scope nat_scope.

(** * Part II: Domain Types *)

(** ** Section 2.1: The Clans

    The Clans are the descendants of the Star League Defense Force who
    followed General Aleksandr Kerensky into exile. Each Clan developed
    unique warrior traditions and combat doctrines.

    - ClanWolf: Wardens who preserved Kerensky's vision of protecting the Inner Sphere
    - ClanJadeFalcon: Aggressive Crusaders, bitter rivals of the Wolves
    - ClanSmokeJaguar: Brutal warriors known for savagery, destroyed in 3060
    - ClanGhostBear: Patient, methodical warriors who value family bonds
    - ClanNovaCat: Mystical warriors guided by visions
    - ClanDiamondShark: Merchant warriors, formerly Sea Fox
    - ClanSteelViper: Traditionalists absorbed by other Clans
    - ClanHellsHorses: Combined-arms specialists favoring vehicles
    - ClanCoyote: Innovators and founders of the OmniMech
    - ClanStarAdder: Careful strategists and political manipulators
    - ClanBloodSpirit: Isolationists, destroyed in the Wars of Reaving
    - ClanFireMandrill: Fractious Clan organized into Kindraa
    - ClanCloudCobra: Religious warriors devoted to "The Way"
    - ClanSnowRaven: Naval specialists and merchant-warriors
    - ClanGoliathScorpion: Seekers of Star League artifacts
    - ClanIceHellion: Swift raiders known for aggressive tactics
*)

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

(** Decidable equality for Clans. *)
Definition clan_eq_dec : forall (c1 c2 : Clan), {c1 = c2} + {c1 <> c2}.
Proof.
  decide equality.
  apply Nat.eq_dec.
Defined.

(** Boolean equality with correctness proof. *)
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

(** ** Section 2.2: Warrior Ranks

    Clan military ranks follow a strict hierarchy. Warriors advance through
    Trials of Position. The touman (military) is organized from Points (5 units)
    up through Stars, Binaries, Trinaries, Clusters, and Galaxies.

    - Warrior: Basic fighter, no command authority
    - Point Commander: Commands a Point (5 units)
    - Star Commander: Commands a Star (5 Points = 25 units)
    - Star Captain: Commands a Binary/Trinary (2-3 Stars)
    - Star Colonel: Commands a Cluster (3-5 Binaries)
    - Galaxy Commander: Commands a Galaxy (3-5 Clusters)
    - Khan: Supreme military commander of a Clan
    - saKhan: Second-in-command, often leads combat operations
    - Loremaster: Keeper of traditions, arbiter of disputes
*)

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

(** Numeric encoding for rank comparison. *)
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

Definition rank_lt (r1 r2 : Rank) : bool :=
  rank_to_nat r1 <? rank_to_nat r2.

Definition rank_eq_dec : forall (r1 r2 : Rank), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.

(** ** Section 2.3: Commanders

    A Commander represents a warrior authorized to issue or respond to batchall.
    Bloodnamed warriors have won a Trial of Bloodright and carry the genetic
    legacy name of an original SLDF warrior who joined the Exodus. *)

Record Commander : Type := mkCommander {
  cmd_id : nat;
  cmd_clan : Clan;
  cmd_rank : Rank;
  cmd_bloodnamed : bool
}.

Definition commander_eq_dec : forall (c1 c2 : Commander), {c1 = c2} + {c1 <> c2}.
Proof.
  decide equality.
  - apply Bool.bool_dec.
  - apply rank_eq_dec.
  - apply clan_eq_dec.
  - apply Nat.eq_dec.
Defined.

(** A commander may issue batchall if they hold appropriate rank. *)
Definition may_issue_batchall (c : Commander) : bool :=
  rank_le StarCaptain (cmd_rank c).

(** ** Section 2.4: Unit Classifications

    Combat units in the Clans are classified by type and weight.

    Unit Classes:
    - OmniMech: Modular BattleMech with swappable weapon pods
    - BattleMech: Standard 'Mech without OmniMech modularity
    - ProtoMech: Small 2-9 ton combat units
    - Aerospace: Conventional aerospace fighters
    - OmniFighter: Modular aerospace fighters
    - Vehicle: Ground combat vehicles
    - BattleArmor: Powered infantry armor (non-Elemental)
    - Elemental: Clan-specific genetically enhanced infantry in battle armor
    - Infantry: Unarmored foot soldiers (dezgra - dishonorable)
*)

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

(** Weight classes determine a unit's tonnage range. *)
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

(** ** Section 2.5: Combat Units

    A Unit represents a single combat asset that can be committed to battle.

    In BattleTech, warrior skills are measured on two axes:
    - Gunnery: Ability to hit targets with weapons (lower is better, 0-7 scale)
    - Piloting: Ability to maneuver and avoid falls (lower is better, 0-7 scale)

    Elite warriors (gunnery + piloting <= 4) are highly prized.
    Green warriors (gunnery + piloting >= 9) are considered unreliable.
*)

Record Unit : Type := mkUnit {
  unit_id : nat;
  unit_class : UnitClass;
  unit_weight : WeightClass;
  unit_tonnage : nat;
  unit_gunnery : nat;
  unit_piloting : nat;
  unit_is_elite : bool;
  unit_is_clan : bool
}.

(** Combined skill rating for backward compatibility and simple comparisons. *)
Definition unit_skill (u : Unit) : nat :=
  unit_gunnery u + unit_piloting u.

(** Skill level classifications based on combined rating. *)
Definition is_elite_skill (u : Unit) : bool :=
  unit_skill u <=? 4.

Definition is_regular_skill (u : Unit) : bool :=
  (4 <? unit_skill u) && (unit_skill u <? 9).

Definition is_green_skill (u : Unit) : bool :=
  9 <=? unit_skill u.

Lemma skill_classification_exhaustive : forall u,
  is_elite_skill u = true \/ is_regular_skill u = true \/ is_green_skill u = true.
Proof.
  intros u. unfold is_elite_skill, is_regular_skill, is_green_skill.
  destruct (unit_skill u <=? 4) eqn:H1.
  - left. reflexivity.
  - destruct (9 <=? unit_skill u) eqn:H2.
    + right. right. reflexivity.
    + right. left. apply andb_true_intro. split.
      * apply Nat.ltb_lt. apply Nat.leb_gt in H1. exact H1.
      * apply Nat.ltb_lt. apply Nat.leb_gt in H2. exact H2.
Qed.

(** A Force is a list of units committed to combat. *)
Definition Force : Type := list Unit.

(** * Part III: Force Metrics and Ordering *)

(** ** Section 3.1: Force Metrics

    Force metrics provide a quantitative summary of a force's combat potential.
    These metrics are used for bid comparison in the batchall ritual.

    - fm_count: Number of units in the force
    - fm_tonnage: Total tonnage of all units
    - fm_elite_count: Number of elite-rated units
    - fm_clan_count: Number of Clan-tech units (vs Inner Sphere salvage)
*)

Record ForceMetrics : Type := mkForceMetrics {
  fm_count : nat;
  fm_tonnage : nat;
  fm_elite_count : nat;
  fm_clan_count : nat
}.

(** The empty force has zero metrics. *)
Definition empty_metrics : ForceMetrics :=
  mkForceMetrics 0 0 0 0.

(** Convert a single unit to its metric contribution. *)
Definition unit_to_metrics (u : Unit) : ForceMetrics :=
  mkForceMetrics
    1
    (unit_tonnage u)
    (if unit_is_elite u then 1 else 0)
    (if unit_is_clan u then 1 else 0).

(** Metrics form a commutative monoid under addition. *)
Definition metrics_add (m1 m2 : ForceMetrics) : ForceMetrics :=
  mkForceMetrics
    (fm_count m1 + fm_count m2)
    (fm_tonnage m1 + fm_tonnage m2)
    (fm_elite_count m1 + fm_elite_count m2)
    (fm_clan_count m1 + fm_clan_count m2).

(** Compute the metrics of a force by folding over units. *)
Definition force_metrics (f : Force) : ForceMetrics :=
  fold_right (fun u acc => metrics_add (unit_to_metrics u) acc) empty_metrics f.

(** ** Section 3.2: Metrics Monoid Laws *)

Lemma metrics_add_comm : forall m1 m2,
  metrics_add m1 m2 = metrics_add m2 m1.
Proof.
  intros [c1 t1 e1 l1] [c2 t2 e2 l2].
  unfold metrics_add. simpl.
  rewrite (Nat.add_comm c1 c2).
  rewrite (Nat.add_comm t1 t2).
  rewrite (Nat.add_comm e1 e2).
  rewrite (Nat.add_comm l1 l2).
  reflexivity.
Qed.

Lemma metrics_add_assoc : forall m1 m2 m3,
  metrics_add m1 (metrics_add m2 m3) = metrics_add (metrics_add m1 m2) m3.
Proof.
  intros [c1 t1 e1 l1] [c2 t2 e2 l2] [c3 t3 e3 l3].
  unfold metrics_add. simpl.
  rewrite (Nat.add_assoc c1 c2 c3).
  rewrite (Nat.add_assoc t1 t2 t3).
  rewrite (Nat.add_assoc e1 e2 e3).
  rewrite (Nat.add_assoc l1 l2 l3).
  reflexivity.
Qed.

Lemma metrics_add_empty_l : forall m,
  metrics_add empty_metrics m = m.
Proof.
  intros [c t e l]. unfold metrics_add, empty_metrics. reflexivity.
Qed.

Lemma metrics_add_empty_r : forall m,
  metrics_add m empty_metrics = m.
Proof.
  intros [c t e l]. unfold metrics_add, empty_metrics. simpl.
  rewrite Nat.add_0_r. rewrite Nat.add_0_r.
  rewrite Nat.add_0_r. rewrite Nat.add_0_r.
  reflexivity.
Qed.

(** ** Section 3.3: Force Metrics Computation *)

Lemma force_metrics_nil : force_metrics [] = empty_metrics.
Proof. reflexivity. Qed.

Lemma force_metrics_cons : forall u f,
  force_metrics (u :: f) = metrics_add (unit_to_metrics u) (force_metrics f).
Proof. reflexivity. Qed.

Lemma force_metrics_app : forall f1 f2,
  force_metrics (f1 ++ f2) = metrics_add (force_metrics f1) (force_metrics f2).
Proof.
  induction f1 as [|u rest IH]; intros f2.
  - simpl. rewrite metrics_add_empty_l. reflexivity.
  - simpl. rewrite IH. rewrite metrics_add_assoc. reflexivity.
Qed.

(** ** Section 3.4: Partial Order on Force Metrics

    Force metrics form a partial order under componentwise comparison.
    This order is used to determine valid bids: a new bid must be
    strictly less than the previous bid in this order. *)

Definition fm_le (m1 m2 : ForceMetrics) : Prop :=
  fm_count m1 <= fm_count m2 /\
  fm_tonnage m1 <= fm_tonnage m2 /\
  fm_elite_count m1 <= fm_elite_count m2 /\
  fm_clan_count m1 <= fm_clan_count m2.

Definition fm_lt (m1 m2 : ForceMetrics) : Prop :=
  fm_le m1 m2 /\ m1 <> m2.

(** Decidability of the ordering. *)
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

Definition fm_eq_dec : forall m1 m2 : ForceMetrics, {m1 = m2} + {m1 <> m2}.
Proof.
  intros [c1 t1 e1 l1] [c2 t2 e2 l2].
  destruct (Nat.eq_dec c1 c2);
  destruct (Nat.eq_dec t1 t2);
  destruct (Nat.eq_dec e1 e2);
  destruct (Nat.eq_dec l1 l2);
  try (left; congruence);
  right; congruence.
Defined.

Definition fm_lt_dec (m1 m2 : ForceMetrics) : {fm_lt m1 m2} + {~ fm_lt m1 m2}.
Proof.
  unfold fm_lt.
  destruct (fm_le_dec m1 m2).
  - destruct (fm_eq_dec m1 m2).
    + right. intros [_ Hneq]. contradiction.
    + left. auto.
  - right. intros [Hle _]. contradiction.
Defined.

(** ** Section 3.5: Partial Order Laws *)

Lemma fm_le_refl : forall m, fm_le m m.
Proof.
  intros m. unfold fm_le. auto.
Qed.

Lemma fm_le_trans : forall m1 m2 m3,
  fm_le m1 m2 -> fm_le m2 m3 -> fm_le m1 m3.
Proof.
  intros m1 m2 m3 [H1a [H1b [H1c H1d]]] [H2a [H2b [H2c H2d]]].
  unfold fm_le. repeat split; lia.
Qed.

Lemma fm_le_antisym : forall m1 m2,
  fm_le m1 m2 -> fm_le m2 m1 -> m1 = m2.
Proof.
  intros [c1 t1 e1 l1] [c2 t2 e2 l2].
  unfold fm_le. simpl.
  intros [H1a [H1b [H1c H1d]]] [H2a [H2b [H2c H2d]]].
  f_equal; lia.
Qed.

(** ** Section 3.6: Well-Founded Order

    The key property for termination: the strict order on metrics is
    well-founded. This ensures bidding cannot continue forever. *)

Definition fm_measure (m : ForceMetrics) : nat :=
  fm_count m + fm_tonnage m + fm_elite_count m + fm_clan_count m.

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

Theorem fm_lt_well_founded : well_founded fm_lt.
Proof.
  apply well_founded_lt_compat with (f := fm_measure).
  intros m1 m2 Hlt. apply fm_lt_implies_measure_lt. exact Hlt.
Qed.

(** ** Section 3.7: Force Ordering *)

Definition force_le (f1 f2 : Force) : Prop :=
  fm_le (force_metrics f1) (force_metrics f2).

Definition force_lt (f1 f2 : Force) : Prop :=
  fm_lt (force_metrics f1) (force_metrics f2).

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

(** * Part IV: Trials, Stakes, and Honor Codes *)

(** ** Section 4.1: Trial Types

    Clan society revolves around ritualized combat trials. Each trial type
    serves a specific purpose and carries different stakes and honor implications.

    - TrialOfPosition: Advancement in rank; warriors challenge superiors
    - TrialOfPossession: Claim resources, territory, bondsmen, or equipment
    - TrialOfRefusal: Protest a political or military decision
    - TrialOfGrievance: Personal dispute resolution between warriors
    - TrialOfBloodright: Competition for a Bloodname legacy
    - TrialOfAbjuration: Exile a warrior or unit from the Clan
    - TrialOfAnnihilation: Total destruction of target (extremely rare)
*)

Inductive TrialType : Type :=
  | TrialOfPosition
  | TrialOfPossession
  | TrialOfRefusal
  | TrialOfGrievance
  | TrialOfBloodright
  | TrialOfAbjuration
  | TrialOfAnnihilation.

Definition trial_eq_dec : forall t1 t2 : TrialType, {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

(** Severity determines the stakes and scrutiny applied to the trial. *)
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

(** Some trials require a Circle of Equals - observed by peer warriors. *)
Definition trial_requires_circle (t : TrialType) : bool :=
  match t with
  | TrialOfBloodright => true
  | TrialOfAnnihilation => true
  | _ => false
  end.

(** Annihilation trials are explicitly lethal - no hegira permitted. *)
Definition trial_is_lethal (t : TrialType) : bool :=
  match t with
  | TrialOfAnnihilation => true
  | _ => false
  end.

Lemma trial_severity_positive : forall t, trial_severity t >= 1.
Proof. intros t. destruct t; simpl; lia. Qed.

Lemma annihilation_most_severe : forall t,
  trial_severity t <= trial_severity TrialOfAnnihilation.
Proof. intros t. destruct t; simpl; lia. Qed.

(** ** Section 4.2: Prizes and Stakes

    The prize is what the challenger seeks to claim through the batchall. *)

Inductive Prize : Type :=
  | PrizeWorld (world_id : nat)
  | PrizeEnclave (enclave_id : nat)
  | PrizeFacility (facility_id : nat)
  | PrizeBloodright (bloodname_id : nat)
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

(** ** Section 4.3: Zellbrigen - The Dueling Honor Code

    Zellbrigen is the Clan code of honorable one-on-one combat. Warriors
    declare targets, engage individually, and respect fallen opponents.
    Violation of Zellbrigen brings severe dishonor.

    Key rules:
    - One-on-one engagement (no "gang up" tactics)
    - No physical attacks (punching/kicking 'Mechs is dezgra)
    - Declare targets before engaging
    - Respect ejected pilots (no attacking ejection pods)
*)

Inductive ZellbrigenStatus : Type :=
  | ZellActive
  | ZellBroken (violator_id : nat)
  | ZellSuspended
  | ZellNotApplicable.

Record ZellbrigenRules : Type := mkZellbrigenRules {
  zell_one_on_one : bool;
  zell_no_physical : bool;
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

Lemma zell_violation_positive : forall v, zell_violation_severity v >= 1.
Proof. intros v. destruct v; simpl; lia. Qed.

(** ** Section 4.4: Safcon - Safe Conduct Protocol

    Safcon (safe conduct) protects DropShips and JumpShips traveling to
    and from a battle. Attacking vessels under safcon is severely dishonorable.
*)

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

Lemma safcon_default_active : forall c, safcon_active (default_safcon c) = true.
Proof. intros c. reflexivity. Qed.

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

Lemma safcon_violation_dishonorable : forall v,
  safcon_violation_dishonor v >= 3.
Proof. intros v. destruct v; simpl; lia. Qed.

(** Dynamic safcon state for tracking time-dependent expiration. *)
Record SafconState : Type := mkSafconState {
  safcon_terms : SafconTerms;
  safcon_remaining_hours : nat;
  safcon_status : SafconStatus
}.

Definition init_safcon_state (terms : SafconTerms) : SafconState :=
  mkSafconState terms (safcon_duration_hours terms)
    (if safcon_granted terms then SafconGranted else SafconDenied).

Definition tick_safcon (s : SafconState) (hours : nat) : SafconState :=
  let remaining := safcon_remaining_hours s - hours in
  let new_status := if Nat.eqb remaining 0
                    then SafconExpired
                    else safcon_status s in
  mkSafconState (safcon_terms s) remaining new_status.

Definition safcon_state_active (s : SafconState) : bool :=
  match safcon_status s with
  | SafconGranted => negb (Nat.eqb (safcon_remaining_hours s) 0)
  | _ => false
  end.

Lemma tick_decreases_remaining : forall s h,
  h <= safcon_remaining_hours s ->
  safcon_remaining_hours (tick_safcon s h) = safcon_remaining_hours s - h.
Proof.
  intros s h Hle. unfold tick_safcon. simpl. reflexivity.
Qed.

Lemma safcon_eventually_expires : forall s,
  safcon_status s = SafconGranted ->
  safcon_status (tick_safcon s (safcon_remaining_hours s)) = SafconExpired.
Proof.
  intros s Hgranted. unfold tick_safcon. simpl.
  rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma init_safcon_preserves_duration : forall terms,
  safcon_remaining_hours (init_safcon_state terms) = safcon_duration_hours terms.
Proof.
  intros terms. reflexivity.
Qed.

(** ** Section 4.5: Hegira - Honorable Retreat

    Hegira is the right to withdraw from battle with honor intact.
    A defender may request hegira if they acknowledge defeat.
    The attacker may grant or deny; denial is dishonorable.
    Violating granted hegira (attacking retreating forces) is severely dishonorable.
*)

Inductive HegiraAction : Type :=
  | HegiraRequest
  | HegiraGrant
  | HegiraDeny
  | HegiraAccept
  | HegiraViolate.

(** ** Section 4.6: Battle Context

    A BattleContext combines all the contextual rules governing a specific
    batchall: the trial type, zellbrigen rules, safcon terms, and whether
    hegira is permitted. Validation predicates ensure consistency. *)

Record BattleContext : Type := mkBattleContext {
  ctx_trial : TrialType;
  ctx_zellbrigen : ZellbrigenRules;
  ctx_safcon : SafconTerms;
  ctx_hegira_allowed : bool;
  ctx_circle_present : bool
}.

(** Derive appropriate zellbrigen rules from trial type. *)
Definition trial_default_zellbrigen (t : TrialType) : ZellbrigenRules :=
  match t with
  | TrialOfAnnihilation => relaxed_zellbrigen
  | _ => strict_zellbrigen
  end.

(** A context is valid if it respects the constraints of its trial type. *)
Definition context_valid (ctx : BattleContext) : Prop :=
  (trial_is_lethal (ctx_trial ctx) = true -> ctx_hegira_allowed ctx = false) /\
  (trial_requires_circle (ctx_trial ctx) = true -> ctx_circle_present ctx = true) /\
  (safcon_active (ctx_safcon ctx) = true -> True).

(** Boolean version for decidable checking. *)
Definition context_valid_b (ctx : BattleContext) : bool :=
  (negb (trial_is_lethal (ctx_trial ctx)) || negb (ctx_hegira_allowed ctx)) &&
  (negb (trial_requires_circle (ctx_trial ctx)) || ctx_circle_present ctx) &&
  true.

Lemma context_valid_b_correct : forall ctx,
  context_valid_b ctx = true <-> context_valid ctx.
Proof.
  intros ctx. unfold context_valid_b, context_valid.
  split.
  - intros H.
    apply andb_prop in H. destruct H as [H1 H2].
    apply andb_prop in H1. destruct H1 as [H1a H1b].
    repeat split; auto.
    + intros Hlethal.
      destruct (ctx_hegira_allowed ctx) eqn:Hheg; auto.
      rewrite Hlethal in H1a. simpl in H1a. discriminate.
    + intros Hcircle.
      destruct (ctx_circle_present ctx) eqn:Hpres; auto.
      rewrite Hcircle in H1b. simpl in H1b. discriminate.
  - intros [H1 [H2 _]].
    apply andb_true_intro. split.
    + apply andb_true_intro. split.
      * destruct (trial_is_lethal (ctx_trial ctx)) eqn:Hlet.
        -- specialize (H1 eq_refl). rewrite H1. reflexivity.
        -- reflexivity.
      * destruct (trial_requires_circle (ctx_trial ctx)) eqn:Hcirc.
        -- specialize (H2 eq_refl). rewrite H2. reflexivity.
        -- reflexivity.
    + reflexivity.
Qed.

(** Annihilation trials never permit hegira in valid contexts. *)
Lemma annihilation_no_hegira : forall ctx,
  context_valid ctx ->
  ctx_trial ctx = TrialOfAnnihilation ->
  ctx_hegira_allowed ctx = false.
Proof.
  intros ctx [Hlethal _] Htrial.
  apply Hlethal. rewrite Htrial. reflexivity.
Qed.

(** Bloodright trials require a circle of equals in valid contexts. *)
Lemma bloodright_requires_circle : forall ctx,
  context_valid ctx ->
  ctx_trial ctx = TrialOfBloodright ->
  ctx_circle_present ctx = true.
Proof.
  intros ctx [_ [Hcircle _]] Htrial.
  apply Hcircle. rewrite Htrial. reflexivity.
Qed.

(** Standard context for typical Trials of Possession. *)
Definition standard_possession_context (grantor : Clan) : BattleContext :=
  mkBattleContext
    TrialOfPossession
    strict_zellbrigen
    (default_safcon grantor)
    true
    false.

Lemma standard_possession_valid : forall c,
  context_valid (standard_possession_context c).
Proof.
  intros c. unfold context_valid, standard_possession_context. simpl.
  repeat split; intros; discriminate.
Qed.

(** Context for Trials of Annihilation - no mercy. *)
Definition annihilation_context (grantor : Clan) : BattleContext :=
  mkBattleContext
    TrialOfAnnihilation
    relaxed_zellbrigen
    (default_safcon grantor)
    false
    true.

Lemma annihilation_context_valid : forall c,
  context_valid (annihilation_context c).
Proof.
  intros c. unfold context_valid, annihilation_context. simpl.
  repeat split; auto.
Qed.

(** * Part V: Protocol Messages and Actions *)

(** ** Section 5.1: Sides

    Every batchall has two sides: the challenger (attacker) who issues
    the batchall, and the defender who must respond. *)

Inductive Side : Type := Attacker | Defender.

Definition side_eq_dec : forall s1 s2 : Side, {s1 = s2} + {s1 <> s2}.
Proof. decide equality. Defined.

Definition side_eqb (s1 s2 : Side) : bool :=
  match s1, s2 with
  | Attacker, Attacker => true
  | Defender, Defender => true
  | _, _ => false
  end.

(** ** Section 5.2: Force Bids

    A ForceBid represents a commitment of forces to the battle.
    During bidding, warriors reduce their bids to demonstrate confidence. *)

Record ForceBid : Type := mkForceBid {
  bid_side : Side;
  bid_force : Force;
  bid_commander : Commander
}.

Definition bid_metrics (b : ForceBid) : ForceMetrics :=
  force_metrics (bid_force b).

Definition bid_lt (b1 b2 : ForceBid) : Prop :=
  bid_side b1 = bid_side b2 /\ fm_lt (bid_metrics b1) (bid_metrics b2).

(** ** Section 5.3: Protocol Messages

    The batchall ritual involves structured message exchange. *)

Record BatchallChallenge : Type := mkBatchallChallenge {
  chal_challenger : Commander;
  chal_prize : Prize;
  chal_initial_force : Force
}.

Record BatchallResponse : Type := mkBatchallResponse {
  resp_defender : Commander;
  resp_location : Location;
  resp_force : Force;
  resp_counter_stakes : option Stakes
}.

(** ** Section 5.4: Refusal Reasons

    A defender may refuse a challenge for specific reasons. Some reasons
    are honorable, others carry dishonor. *)

Inductive RefusalReason : Type :=
  | RefusalDishonorableConduct
  | RefusalNoJurisdiction
  | RefusalInvalidChallenger
  | RefusalAlreadyContested
  | RefusalOther (code : nat).

(** ** Section 5.5: Protocol Actions

    All possible actions in the batchall protocol. *)

Inductive ProtocolAction : Type :=
  | ActChallenge (challenge : BatchallChallenge)
  | ActRespond (response : BatchallResponse)
  | ActRefuse (reason : RefusalReason)
  | ActBid (bid : ForceBid)
  | ActPass (side : Side)
  | ActClose
  | ActBreakBid
  | ActWithdraw (side : Side).

(** * Part VI: State Machine and Transitions *)

(** ** Section 6.1: Ready Status

    During bidding, each side may signal readiness to accept current bids.
    When both sides pass consecutively, bidding concludes. *)

Inductive ReadyStatus : Type :=
  | NeitherReady
  | AttackerReady
  | DefenderReady
  | BothReady.

(** ** Section 6.2: Protocol Phases

    The batchall protocol progresses through well-defined phases. *)

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

(** ** Section 6.3: Transition Rules

    The core state machine defining valid protocol transitions.
    Each constructor represents one valid state transition. *)

Inductive BatchallStep : BatchallPhase -> ProtocolAction -> BatchallPhase -> Prop :=

  | StepChallenge : forall chal,
      BatchallStep PhaseIdle
                   (ActChallenge chal)
                   (PhaseChallenged chal)

  | StepRefuse : forall chal reason,
      BatchallStep (PhaseChallenged chal)
                   (ActRefuse reason)
                   (PhaseRefused chal reason)

  | StepRespond : forall chal resp,
      BatchallStep (PhaseChallenged chal)
                   (ActRespond resp)
                   (PhaseResponded chal resp)

  | StepStartBidding : forall chal resp,
      let atk_bid := mkForceBid Attacker (chal_initial_force chal) (chal_challenger chal) in
      let def_bid := mkForceBid Defender (resp_force resp) (resp_defender resp) in
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

  | StepBothReadyFromAttacker : forall chal resp atk_bid def_bid hist,
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist AttackerReady)
                   (ActPass Defender)
                   (PhaseBidding chal resp atk_bid def_bid hist BothReady)

  | StepBothReadyFromDefender : forall chal resp atk_bid def_bid hist,
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist DefenderReady)
                   (ActPass Attacker)
                   (PhaseBidding chal resp atk_bid def_bid hist BothReady)

  | StepClose : forall chal resp atk_bid def_bid hist,
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist BothReady)
                   ActClose
                   (PhaseAgreed chal resp atk_bid def_bid)

  | StepWithdraw : forall chal resp atk_bid def_bid hist ready side,
      BatchallStep (PhaseBidding chal resp atk_bid def_bid hist ready)
                   (ActWithdraw side)
                   PhaseAborted.

(** ** Section 6.4: Protocol Traces

    A trace is a sequence of valid transitions from a starting phase. *)

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

(** ** Section 6.5: Phase Predicates *)

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

Definition is_terminal_dec (phase : BatchallPhase) : {is_terminal phase} + {~ is_terminal phase}.
Proof.
  destruct phase; simpl; auto; right; auto.
Defined.

(** ** Section 6.6: Extended Protocol State with Safcon and Zellbrigen

    The core BatchallStep relation models the bidding protocol.
    This section extends it with safcon and zellbrigen state tracking,
    creating a richer protocol state that enforces honor rules. *)

Record ExtendedState : Type := mkExtendedState {
  ext_phase : BatchallPhase;
  ext_context : BattleContext;
  ext_safcon : SafconState;
  ext_zellbrigen : ZellbrigenStatus
}.

Definition init_extended_state (ctx : BattleContext) : ExtendedState :=
  mkExtendedState
    PhaseIdle
    ctx
    (init_safcon_state (ctx_safcon ctx))
    ZellActive.

(** Extended actions include safcon/zellbrigen violations. *)
Inductive ExtendedAction : Type :=
  | EActProtocol (action : ProtocolAction)
  | EActSafconViolation (violation : SafconViolationType) (violator : Side)
  | EActZellbrigenViolation (violation : ZellbrigenViolation) (violator : Side)
  | EActTimeTick (hours : nat).

(** Zellbrigen can only be broken, not restored during a trial. *)
Definition update_zellbrigen (current : ZellbrigenStatus) (violation : ZellbrigenViolation)
    (violator_id : nat) : ZellbrigenStatus :=
  match current with
  | ZellActive => ZellBroken violator_id
  | _ => current
  end.

(** Extended step relation: wraps BatchallStep with context enforcement. *)
Inductive ExtendedStep : ExtendedState -> ExtendedAction -> ExtendedState -> Prop :=

  | EStepProtocol : forall phase1 phase2 action ctx safcon zell,
      BatchallStep phase1 action phase2 ->
      ExtendedStep (mkExtendedState phase1 ctx safcon zell)
                   (EActProtocol action)
                   (mkExtendedState phase2 ctx safcon zell)

  | EStepSafconViolation : forall phase ctx safcon zell violation side,
      safcon_state_active safcon = true ->
      ExtendedStep (mkExtendedState phase ctx safcon zell)
                   (EActSafconViolation violation side)
                   (mkExtendedState PhaseAborted ctx
                      (mkSafconState (safcon_terms safcon) 0
                         (SafconViolated (match side with Attacker => 0 | Defender => 1 end)))
                      zell)

  | EStepZellbrigenViolation : forall phase ctx safcon violation side violator_id,
      ExtendedStep (mkExtendedState phase ctx safcon ZellActive)
                   (EActZellbrigenViolation violation side)
                   (mkExtendedState phase ctx safcon (ZellBroken violator_id))

  | EStepTimeTick : forall phase ctx safcon zell hours,
      ExtendedStep (mkExtendedState phase ctx safcon zell)
                   (EActTimeTick hours)
                   (mkExtendedState phase ctx (tick_safcon safcon hours) zell).

(** ** Section 6.6b: Extended State Invariants *)

Definition extended_state_valid (s : ExtendedState) : Prop :=
  context_valid (ext_context s) /\
  (ext_zellbrigen s = ZellActive \/
   exists vid, ext_zellbrigen s = ZellBroken vid \/
               ext_zellbrigen s = ZellSuspended \/
               ext_zellbrigen s = ZellNotApplicable).

Lemma init_extended_state_valid : forall ctx,
  context_valid ctx ->
  extended_state_valid (init_extended_state ctx).
Proof.
  intros ctx Hctx.
  unfold extended_state_valid, init_extended_state. simpl.
  split.
  - exact Hctx.
  - left. reflexivity.
Qed.

Lemma extended_step_preserves_context : forall s1 action s2,
  ExtendedStep s1 action s2 ->
  ext_context s1 = ext_context s2.
Proof.
  intros s1 action s2 Hstep.
  inversion Hstep; reflexivity.
Qed.

Lemma safcon_violation_aborts : forall s1 violation side s2,
  ExtendedStep s1 (EActSafconViolation violation side) s2 ->
  ext_phase s2 = PhaseAborted.
Proof.
  intros s1 violation side s2 Hstep.
  inversion Hstep. reflexivity.
Qed.

Lemma zellbrigen_violation_breaks : forall s1 violation side s2,
  ExtendedStep s1 (EActZellbrigenViolation violation side) s2 ->
  exists vid, ext_zellbrigen s2 = ZellBroken vid.
Proof.
  intros s1 violation side s2 Hstep.
  inversion Hstep. eexists. reflexivity.
Qed.

(** Once zellbrigen is broken, protocol actions still proceed but dishonorably. *)
Lemma protocol_continues_after_zell_break : forall phase1 phase2 action ctx safcon vid,
  BatchallStep phase1 action phase2 ->
  ExtendedStep (mkExtendedState phase1 ctx safcon (ZellBroken vid))
               (EActProtocol action)
               (mkExtendedState phase2 ctx safcon (ZellBroken vid)).
Proof.
  intros. constructor. assumption.
Qed.

(** * Part VII: Honor Accounting System *)

(** ** Section 7.1: Honor Type and Ledger

    Honor is tracked as signed integers - warriors can gain or lose honor.
    The ledger uses a finite map (association list) keyed by cmd_id.

    Design rationale for finite map vs function representation:
    - Finite maps are enumerable (we can list all warriors with honor)
    - Finite maps have decidable domain membership
    - Finite maps support efficient lookup and update operations
    - Finite maps extract cleanly to OCaml/Haskell *)

Open Scope Z_scope.

Definition Honor : Type := Z.

Definition HonorEntry : Type := (nat * Honor)%type.

Definition HonorLedger : Type := list HonorEntry.

(** Lookup honor for a warrior by cmd_id. Returns 0 if not found. *)
Fixpoint ledger_lookup (ledger : HonorLedger) (warrior_id : nat) : Honor :=
  match ledger with
  | [] => 0
  | (id, h) :: rest =>
      if Nat.eqb id warrior_id then h else ledger_lookup rest warrior_id
  end.

(** Lookup honor for a commander (convenience wrapper). *)
Definition ledger_honor (ledger : HonorLedger) (c : Commander) : Honor :=
  ledger_lookup ledger (cmd_id c).

(** Update or insert an entry in the ledger. *)
Fixpoint ledger_update_by_id (ledger : HonorLedger) (warrior_id : nat) (new_honor : Honor)
    : HonorLedger :=
  match ledger with
  | [] => [(warrior_id, new_honor)]
  | (id, h) :: rest =>
      if Nat.eqb id warrior_id
      then (id, new_honor) :: rest
      else (id, h) :: ledger_update_by_id rest warrior_id new_honor
  end.

(** Check if a warrior is in the ledger. *)
Fixpoint ledger_mem (ledger : HonorLedger) (warrior_id : nat) : bool :=
  match ledger with
  | [] => false
  | (id, _) :: rest =>
      if Nat.eqb id warrior_id then true else ledger_mem rest warrior_id
  end.

(** Get all warrior IDs in the ledger. *)
Definition ledger_ids (ledger : HonorLedger) : list nat :=
  map fst ledger.

(** Get the number of warriors tracked. *)
Definition ledger_size (ledger : HonorLedger) : nat :=
  length ledger.

(** The empty ledger. *)
Definition empty_ledger : HonorLedger := [].

(** ** Section 7.1b: Ledger Lookup Lemmas *)

Lemma ledger_lookup_empty : forall id, ledger_lookup empty_ledger id = 0.
Proof. reflexivity. Qed.

Lemma ledger_lookup_head_eq : forall id h rest,
  ledger_lookup ((id, h) :: rest) id = h.
Proof.
  intros id h rest. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma ledger_lookup_head_neq : forall id id' h rest,
  id <> id' ->
  ledger_lookup ((id, h) :: rest) id' = ledger_lookup rest id'.
Proof.
  intros id id' h rest Hneq. simpl.
  destruct (Nat.eqb id id') eqn:Heq.
  - apply Nat.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

(** ** Section 7.1c: Ledger Update Lemmas *)

Lemma ledger_update_lookup_same : forall ledger id h,
  ledger_lookup (ledger_update_by_id ledger id h) id = h.
Proof.
  induction ledger as [| [id' h'] rest IH]; intros id h.
  - simpl. rewrite Nat.eqb_refl. reflexivity.
  - simpl. destruct (Nat.eqb id' id) eqn:Heq.
    + simpl. rewrite Heq. reflexivity.
    + simpl. rewrite Heq. apply IH.
Qed.

Lemma ledger_update_lookup_other : forall ledger id id' h,
  id <> id' ->
  ledger_lookup (ledger_update_by_id ledger id h) id' = ledger_lookup ledger id'.
Proof.
  induction ledger as [| [id'' h''] rest IH]; intros id id' h Hneq.
  - simpl. destruct (Nat.eqb id id') eqn:Heq.
    + apply Nat.eqb_eq in Heq. contradiction.
    + reflexivity.
  - simpl. destruct (Nat.eqb id'' id) eqn:Heq1.
    + simpl. destruct (Nat.eqb id'' id') eqn:Heq2.
      * apply Nat.eqb_eq in Heq1. apply Nat.eqb_eq in Heq2.
        subst. contradiction.
      * reflexivity.
    + simpl. destruct (Nat.eqb id'' id') eqn:Heq2.
      * reflexivity.
      * apply IH. exact Hneq.
Qed.

Lemma ledger_mem_update : forall ledger id h,
  ledger_mem (ledger_update_by_id ledger id h) id = true.
Proof.
  induction ledger as [| [id' h'] rest IH]; intros id h.
  - simpl. rewrite Nat.eqb_refl. reflexivity.
  - simpl. destruct (Nat.eqb id' id) eqn:Heq.
    + simpl. rewrite Heq. reflexivity.
    + simpl. rewrite Heq. apply IH.
Qed.

(** ** Section 7.2: Unified Honor Events

    All honor-affecting events are unified into a single type.
    This ensures consistent honor accounting across all game systems. *)

Inductive HonorEvent : Type :=
  | HEvProtocol (action : ProtocolAction)
  | HEvZellbrigen (violation : ZellbrigenViolation)
  | HEvSafcon (violation : SafconViolationType)
  | HEvHegira (action : HegiraAction).

(** ** Section 7.3: Refusal Honor Deltas

    Different refusal reasons carry different honor implications. *)

Definition refusal_honor_delta (reason : RefusalReason) : Honor :=
  match reason with
  | RefusalDishonorableConduct => 2
  | RefusalNoJurisdiction => 0
  | RefusalInvalidChallenger => 1
  | RefusalAlreadyContested => 0
  | RefusalOther _ => -1
  end.

(** ** Section 7.4: Hegira Honor Deltas *)

Definition hegira_honor_delta (h : HegiraAction) : Honor :=
  match h with
  | HegiraRequest => 0
  | HegiraGrant => 3
  | HegiraDeny => -2
  | HegiraAccept => 1
  | HegiraViolate => -15
  end.

(** ** Section 7.5: Protocol Action Honor Deltas *)

Definition protocol_honor_delta (action : ProtocolAction) : Honor :=
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

(** ** Section 7.6: Unified Honor Delta *)

Definition honor_event_delta (event : HonorEvent) : Honor :=
  match event with
  | HEvProtocol action => protocol_honor_delta action
  | HEvZellbrigen v => Z.opp (Z.of_nat (zell_violation_severity v))
  | HEvSafcon v => Z.opp (Z.of_nat (safcon_violation_dishonor v))
  | HEvHegira h => hegira_honor_delta h
  end.

(** ** Section 7.7: Ledger Updates

    IMPORTANT: The honor ledger keys on cmd_id ONLY.

    Two Commander records with the same cmd_id are considered the same
    warrior for honor tracking purposes, regardless of other fields
    (clan, rank, bloodnamed status). This design choice means:

    1. A warrior's honor persists across promotions (rank changes)
    2. A warrior's honor persists if captured and assigned to a new clan
    3. The cmd_id serves as the unique warrior identifier

    This matches the Clan concept of honor as an individual property
    that follows a warrior throughout their career. *)

Definition update_honor (ledger : HonorLedger) (actor : Commander) (delta : Honor)
    : HonorLedger :=
  let current := ledger_honor ledger actor in
  ledger_update_by_id ledger (cmd_id actor) (current + delta).

Definition apply_event_honor (ledger : HonorLedger) (event : HonorEvent)
    (actor : Commander) : HonorLedger :=
  update_honor ledger actor (honor_event_delta event).

(** ** Section 7.8: Honor Lemmas

    These lemmas establish the keying semantics of the honor ledger. *)

Lemma honor_update_self : forall ledger actor delta,
  ledger_honor (update_honor ledger actor delta) actor =
  (ledger_honor ledger actor + delta)%Z.
Proof.
  intros ledger actor delta.
  unfold update_honor, ledger_honor.
  apply ledger_update_lookup_same.
Qed.

Lemma honor_update_other : forall ledger actor other delta,
  cmd_id actor <> cmd_id other ->
  ledger_honor (update_honor ledger actor delta) other =
  ledger_honor ledger other.
Proof.
  intros ledger actor other delta Hneq.
  unfold update_honor, ledger_honor.
  apply ledger_update_lookup_other. exact Hneq.
Qed.

Lemma hegira_grant_honorable : (hegira_honor_delta HegiraGrant > 0)%Z.
Proof. simpl. lia. Qed.

Lemma hegira_violate_severely_dishonorable :
  (hegira_honor_delta HegiraViolate <= -10)%Z.
Proof. simpl. lia. Qed.

(** Honor is shared between commanders with the same ID (keying lemma). *)
Lemma honor_shared_by_same_id : forall ledger c1 c2 delta,
  cmd_id c1 = cmd_id c2 ->
  ledger_honor (update_honor ledger c1 delta) c2 =
  (ledger_honor ledger c2 + delta)%Z.
Proof.
  intros ledger c1 c2 delta Hid.
  unfold update_honor, ledger_honor.
  rewrite <- Hid.
  apply ledger_update_lookup_same.
Qed.

Close Scope Z_scope.

(** * Part VIII: Internal Clan Bidding *)

(** ** Section 8.1: Internal Bidding Concepts

    When a Clan wins the right to a batchall, internal bidding determines
    which warrior actually leads the force. Warriors compete by bidding
    down their requested forces - the lowest bid wins the honor of combat. *)

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

(** ** Section 8.2: Sequential Internal Bidding *)

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

(** ** Section 8.3: Concurrent Internal Bidding

    For larger operations, multiple warriors may submit bids simultaneously.
    The best bid wins by lexicographic ordering:
    1. Lowest metrics (componentwise)
    2. If equal, lowest priority value (higher rank bids first)
    3. If still equal, earliest timestamp (first to bid wins) *)

Record ConcurrentBid : Type := mkConcurrentBid {
  cbid_candidate : InternalCandidate;
  cbid_timestamp : nat;
  cbid_priority : nat
}.

Definition cbid_metrics (cb : ConcurrentBid) : ForceMetrics :=
  icand_metrics (cbid_candidate cb).

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
              then (if cbid_priority cb <? cbid_priority acc then cb
                    else if cbid_priority acc <? cbid_priority cb then acc
                    else if cbid_timestamp cb <? cbid_timestamp acc then cb
                    else acc)
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

(** ** Section 8.3b: Explicit Bid Comparison

    For clarity, we define an explicit comparison predicate that makes
    the bid ordering transparent. This predicate expresses when one
    bid is "better" (should win) over another according to the Clan
    bidding rules:

    1. Lower force metrics (componentwise)
    2. If metrics are equal, higher priority (lower priority number = more senior)
    3. If priority is equal, earlier timestamp (first to bid wins) *)

Definition cbid_better (b1 b2 : ConcurrentBid) : bool :=
  if fm_lt_dec (cbid_metrics b1) (cbid_metrics b2) then true
  else if fm_lt_dec (cbid_metrics b2) (cbid_metrics b1) then false
  else if cbid_priority b1 <? cbid_priority b2 then true
  else if cbid_priority b2 <? cbid_priority b1 then false
  else cbid_timestamp b1 <=? cbid_timestamp b2.

Definition cbid_compare (b1 b2 : ConcurrentBid) : ConcurrentBid :=
  if cbid_better b1 b2 then b1 else b2.

Lemma cbid_compare_choice : forall b1 b2,
  cbid_compare b1 b2 = b1 \/ cbid_compare b1 b2 = b2.
Proof.
  intros b1 b2. unfold cbid_compare.
  destruct (cbid_better b1 b2); auto.
Qed.

Lemma cbid_better_refl : forall b, cbid_better b b = true.
Proof.
  intros b. unfold cbid_better.
  destruct (fm_lt_dec (cbid_metrics b) (cbid_metrics b)) as [[Hle Hneq] | Hnlt].
  - exfalso. apply Hneq. reflexivity.
  - destruct (fm_lt_dec (cbid_metrics b) (cbid_metrics b)) as [[Hle' Hneq'] | Hnlt'].
    + exfalso. apply Hneq'. reflexivity.
    + destruct (cbid_priority b <? cbid_priority b) eqn:Hp1.
      * apply Nat.ltb_lt in Hp1. lia.
      * destruct (cbid_priority b <? cbid_priority b) eqn:Hp2.
        -- apply Nat.ltb_lt in Hp2. lia.
        -- apply Nat.leb_refl.
Qed.

Lemma cbid_compare_self : forall b, cbid_compare b b = b.
Proof.
  intros b. unfold cbid_compare.
  rewrite cbid_better_refl. reflexivity.
Qed.

Lemma cbid_better_total : forall b1 b2,
  cbid_better b1 b2 = true \/ cbid_better b2 b1 = true.
Proof.
  intros b1 b2. unfold cbid_better.
  destruct (fm_lt_dec (cbid_metrics b1) (cbid_metrics b2)).
  - left. reflexivity.
  - destruct (fm_lt_dec (cbid_metrics b2) (cbid_metrics b1)).
    + right. reflexivity.
    + destruct (cbid_priority b1 <? cbid_priority b2) eqn:Hp12.
      * left. reflexivity.
      * destruct (cbid_priority b2 <? cbid_priority b1) eqn:Hp21.
        -- right. reflexivity.
        -- destruct (cbid_timestamp b1 <=? cbid_timestamp b2) eqn:Ht12.
           ++ left. reflexivity.
           ++ right. apply Nat.leb_nle in Ht12. apply Nat.leb_le. lia.
Qed.

(** ** Section 8.4: find_best_bid Correctness *)

Lemma find_best_bid_nonempty : forall bids,
  bids <> [] -> exists winner, find_best_bid bids = Some winner.
Proof.
  intros bids Hne.
  destruct bids as [|b rest].
  - contradiction.
  - simpl. eexists. reflexivity.
Qed.

Definition cbid_select (acc cb : ConcurrentBid) : ConcurrentBid :=
  if fm_le_dec (cbid_metrics cb) (cbid_metrics acc)
  then (if fm_le_dec (cbid_metrics acc) (cbid_metrics cb)
        then (if cbid_priority cb <? cbid_priority acc then cb
              else if cbid_priority acc <? cbid_priority cb then acc
              else if cbid_timestamp cb <? cbid_timestamp acc then cb
              else acc)
        else cb)
  else acc.

Lemma cbid_select_In_pair : forall a b,
  cbid_select a b = a \/ cbid_select a b = b.
Proof.
  intros a b. unfold cbid_select.
  destruct (fm_le_dec (cbid_metrics b) (cbid_metrics a)).
  - destruct (fm_le_dec (cbid_metrics a) (cbid_metrics b)).
    + destruct (cbid_priority b <? cbid_priority a) eqn:Hp1; auto.
      destruct (cbid_priority a <? cbid_priority b) eqn:Hp2; auto.
      destruct (cbid_timestamp b <? cbid_timestamp a); auto.
    + auto.
  - auto.
Qed.

Lemma fold_left_In_init_or_rest : forall (l : list ConcurrentBid) (init : ConcurrentBid),
  fold_left cbid_select l init = init \/ In (fold_left cbid_select l init) l.
Proof.
  induction l as [|x rest IH]; intros init.
  - simpl. left. reflexivity.
  - simpl. specialize (IH (cbid_select init x)).
    destruct IH as [Heq | Hin].
    + destruct (cbid_select_In_pair init x) as [Heq' | Heq'].
      * left. rewrite Heq. exact Heq'.
      * right. left. rewrite Heq. rewrite Heq'. reflexivity.
    + right. right. exact Hin.
Qed.

Lemma fold_left_In_invariant : forall (l : list ConcurrentBid) (init : ConcurrentBid),
  In (fold_left cbid_select l init) (init :: l).
Proof.
  intros l init.
  destruct (fold_left_In_init_or_rest l init) as [Heq | Hin].
  - rewrite Heq. left. reflexivity.
  - right. exact Hin.
Qed.

Lemma find_best_bid_eq_fold : forall b rest,
  find_best_bid (b :: rest) = Some (fold_left cbid_select rest b).
Proof.
  intros b rest. simpl. f_equal.
Qed.

Lemma find_best_bid_In : forall bids winner,
  find_best_bid bids = Some winner -> In winner bids.
Proof.
  intros bids winner Hfind.
  destruct bids as [|b rest].
  - simpl in Hfind. discriminate.
  - rewrite find_best_bid_eq_fold in Hfind.
    inversion Hfind as [Heq]. subst winner. clear Hfind.
    apply fold_left_In_invariant.
Qed.

Theorem find_best_bid_correct : forall bids winner,
  find_best_bid bids = Some winner -> In winner bids.
Proof.
  intros bids winner Hfind.
  apply find_best_bid_In. exact Hfind.
Qed.

(** * Part IX: Termination and Soundness Proofs *)

(** ** Section 9.1: Terminal States are Final *)

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

(** ** Section 9.2: Protocol Determinism

    Given the same starting phase and action, there is exactly one
    resulting phase. The protocol is deterministic. *)

Theorem protocol_determinism : forall phase action phase1 phase2,
  BatchallStep phase action phase1 ->
  BatchallStep phase action phase2 ->
  phase1 = phase2.
Proof.
  intros phase action phase1 phase2 H1 H2.
  inversion H1; subst; inversion H2; subst; try reflexivity; try discriminate.
  all: try congruence.
Qed.

(** ** Section 9.3: Bidding Measure

    The bidding measure strictly decreases with each bid, ensuring termination. *)

Definition bid_measure (b : ForceBid) : nat := fm_measure (bid_metrics b).

Definition bidding_state_measure (atk_bid def_bid : ForceBid) (ready : ReadyStatus) : nat :=
  let base := 3 * (bid_measure atk_bid + bid_measure def_bid) in
  match ready with
  | NeitherReady => base + 2
  | AttackerReady => base + 1
  | DefenderReady => base + 1
  | BothReady => base
  end.

(** ** Section 9.4: Bidding Steps Decrease Measure *)

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

(** ** Section 9.5: Bidding Step Progress *)

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
  - left. do 4 eexists. split; [reflexivity|].
    unfold bidding_state_measure. lia.
  - left. do 4 eexists. split; [reflexivity|].
    unfold bidding_state_measure. lia.
  - right. simpl. trivial.
  - right. simpl. trivial.
Qed.

(** ** Section 9.6: Bidding Termination *)

Theorem bidding_terminates_by_measure : forall (chal : BatchallChallenge) (resp : BatchallResponse)
    (atk def : ForceBid) (hist : list ForceBid) (ready : ReadyStatus),
  Acc (fun m1 m2 => m1 < m2) (bidding_state_measure atk def ready).
Proof.
  intros. apply Wf_nat.lt_wf.
Qed.

(** ** Section 9.6b: State-Level Bidding Termination (Glue Theorem)

    This is the crucial connection between the abstract measure and the
    actual state machine. We define a step relation on bidding configurations
    and prove it is well-founded, which means every sequence of bidding steps
    must eventually reach a terminal state. *)

Record BiddingConfig : Type := mkBiddingConfig {
  bconf_chal : BatchallChallenge;
  bconf_resp : BatchallResponse;
  bconf_atk : ForceBid;
  bconf_def : ForceBid;
  bconf_hist : list ForceBid;
  bconf_ready : ReadyStatus
}.

Definition bconf_measure (c : BiddingConfig) : nat :=
  bidding_state_measure (bconf_atk c) (bconf_def c) (bconf_ready c).

Definition bidding_config_step (c1 c2 : BiddingConfig) : Prop :=
  exists action,
    BatchallStep (PhaseBidding (bconf_chal c2) (bconf_resp c2)
                               (bconf_atk c2) (bconf_def c2)
                               (bconf_hist c2) (bconf_ready c2))
                 action
                 (PhaseBidding (bconf_chal c1) (bconf_resp c1)
                               (bconf_atk c1) (bconf_def c1)
                               (bconf_hist c1) (bconf_ready c1)).

Lemma bidding_config_step_decreases : forall c1 c2,
  bidding_config_step c1 c2 ->
  bconf_measure c1 < bconf_measure c2.
Proof.
  intros c1 c2 [action Hstep].
  unfold bconf_measure.
  inversion Hstep; subst.
  - apply bid_decrease_implies_measure_decrease.
    apply fm_lt_implies_measure_lt. assumption.
  - apply def_bid_decrease_implies_measure_decrease.
    apply fm_lt_implies_measure_lt. assumption.
  - unfold bidding_state_measure. lia.
  - unfold bidding_state_measure. lia.
  - unfold bidding_state_measure. lia.
  - unfold bidding_state_measure. lia.
Qed.

Theorem bidding_config_well_founded : well_founded bidding_config_step.
Proof.
  apply well_founded_lt_compat with (f := bconf_measure).
  intros c1 c2 Hstep.
  apply bidding_config_step_decreases. exact Hstep.
Qed.

(** Main termination theorem: From any bidding configuration, there is no
    infinite descending chain of bidding steps. *)
Theorem bidding_always_terminates : forall c : BiddingConfig,
  Acc bidding_config_step c.
Proof.
  intros c.
  apply bidding_config_well_founded.
Qed.

(** Corollary: Any sequence of bidding states has bounded length. *)
Corollary bidding_bounded_by_measure : forall c,
  forall seq : nat -> BiddingConfig,
  seq 0 = c ->
  (forall n, bidding_config_step (seq (S n)) (seq n)) ->
  False.
Proof.
  intros c seq Hstart Hdesc.
  assert (Hmono : forall n, bconf_measure (seq n) + n <= bconf_measure c).
  { induction n.
    - rewrite Hstart. lia.
    - specialize (Hdesc n).
      apply bidding_config_step_decreases in Hdesc.
      lia. }
  specialize (Hmono (S (bconf_measure c))).
  lia.
Qed.

(** ** Section 9.7: No Infinite Bidding Sequences *)

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

(** ** Section 9.8: Well-Founded Bid Ordering *)

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

(** ** Section 9.9: Progress Properties (Liveness)

    We prove that from any non-terminal state, at least one action is possible.
    This is the dual of safety (termination) - it ensures the protocol doesn't
    get stuck in a non-terminal state. *)

Theorem idle_has_progress : forall (chal : BatchallChallenge),
  exists phase', BatchallStep PhaseIdle (ActChallenge chal) phase'.
Proof.
  intros chal.
  exists (PhaseChallenged chal).
  constructor.
Qed.

Theorem challenged_has_progress : forall chal,
  (exists resp phase', BatchallStep (PhaseChallenged chal) (ActRespond resp) phase') /\
  (exists reason phase', BatchallStep (PhaseChallenged chal) (ActRefuse reason) phase').
Proof.
  intros chal. split.
  - exists (mkBatchallResponse (mkCommander 0 ClanWolf Warrior false) (LocEnclave 0) [] None).
    eexists. constructor.
  - exists RefusalNoJurisdiction. eexists. constructor.
Qed.

Theorem responded_has_progress : forall chal resp,
  exists action phase', BatchallStep (PhaseResponded chal resp) action phase'.
Proof.
  intros chal resp.
  set (atk_bid := mkForceBid Attacker (chal_initial_force chal) (chal_challenger chal)).
  exists (ActBid atk_bid).
  eexists. constructor.
Qed.

Theorem bidding_has_progress : forall chal resp atk def hist ready,
  exists action phase', BatchallStep (PhaseBidding chal resp atk def hist ready) action phase'.
Proof.
  intros chal resp atk def hist ready.
  destruct ready.
  - exists (ActPass Attacker). eexists. constructor.
  - exists (ActPass Defender). eexists. constructor.
  - exists (ActPass Attacker). eexists. constructor.
  - exists (ActWithdraw Attacker). eexists. constructor.
Qed.

Definition can_progress (phase : BatchallPhase) : Prop :=
  exists action phase', BatchallStep phase action phase'.

Theorem non_terminal_can_progress : forall phase,
  ~ is_terminal phase -> can_progress phase.
Proof.
  intros phase Hnterm.
  unfold can_progress.
  destruct phase as [| chal | chal resp | chal resp atk def hist ready | | |].
  - destruct (idle_has_progress (mkBatchallChallenge
        (mkCommander 0 ClanWolf StarCaptain false) PrizeHonor [])) as [phase' H].
    eexists. eexists. exact H.
  - destruct (challenged_has_progress chal) as [[r [phase' H]] _].
    eexists. eexists. exact H.
  - destruct (responded_has_progress chal resp) as [action [phase' H]].
    eexists. eexists. exact H.
  - destruct (bidding_has_progress chal resp atk def hist ready) as [action [phase' H]].
    eexists. eexists. exact H.
  - simpl in Hnterm. contradiction.
  - simpl in Hnterm. contradiction.
  - simpl in Hnterm. contradiction.
Qed.

(** ** Section 9.9b: Action-Parametric Progress (Strengthened)

    The above proves existential progress (some action exists).
    Here we characterize exactly which actions are valid from each phase,
    providing action-parametric progress: if an action is valid for a phase,
    then there exists a resulting phase.

    This is stronger because it says not just "you can do something" but
    "if you propose a specific valid action, it will definitely work." *)

Definition action_valid_for_idle (action : ProtocolAction) : Prop :=
  match action with
  | ActChallenge _ => True
  | _ => False
  end.

Definition action_valid_for_challenged (action : ProtocolAction) : Prop :=
  match action with
  | ActRespond _ => True
  | ActRefuse _ => True
  | _ => False
  end.

Definition action_valid_for_responded (chal : BatchallChallenge) (resp : BatchallResponse)
    (action : ProtocolAction) : Prop :=
  match action with
  | ActBid bid => bid = mkForceBid Attacker (chal_initial_force chal) (chal_challenger chal)
  | _ => False
  end.

Definition action_valid_for_bidding (atk def : ForceBid) (ready : ReadyStatus)
    (action : ProtocolAction) : Prop :=
  match action with
  | ActBid bid => (bid_side bid = Attacker /\ fm_lt (bid_metrics bid) (bid_metrics atk)) \/
                  (bid_side bid = Defender /\ fm_lt (bid_metrics bid) (bid_metrics def))
  | ActPass Attacker => ready = NeitherReady \/ ready = DefenderReady
  | ActPass Defender => ready = NeitherReady \/ ready = AttackerReady
  | ActClose => ready = BothReady
  | ActWithdraw _ => True
  | _ => False
  end.

(** Main theorem: valid actions always produce a next state. *)
Theorem valid_action_produces_step_idle : forall action,
  action_valid_for_idle action ->
  exists phase', BatchallStep PhaseIdle action phase'.
Proof.
  intros action Hvalid.
  destruct action; simpl in Hvalid; try contradiction.
  exists (PhaseChallenged challenge). constructor.
Qed.

Theorem valid_action_produces_step_challenged : forall chal action,
  action_valid_for_challenged action ->
  exists phase', BatchallStep (PhaseChallenged chal) action phase'.
Proof.
  intros chal action Hvalid.
  destruct action; simpl in Hvalid; try contradiction.
  - exists (PhaseResponded chal response). constructor.
  - exists (PhaseRefused chal reason). constructor.
Qed.

Theorem valid_action_produces_step_responded : forall chal resp action,
  action_valid_for_responded chal resp action ->
  exists phase', BatchallStep (PhaseResponded chal resp) action phase'.
Proof.
  intros chal resp action Hvalid.
  destruct action; simpl in Hvalid; try contradiction.
  subst bid.
  eexists. constructor.
Qed.

(** For bidding, we need to be more careful since bid validity depends on context. *)
Theorem valid_action_produces_step_bidding : forall chal resp atk def hist ready action,
  action_valid_for_bidding atk def ready action ->
  exists phase', BatchallStep (PhaseBidding chal resp atk def hist ready) action phase'.
Proof.
  intros chal resp atk def hist ready action Hvalid.
  destruct action; simpl in Hvalid; try contradiction.
  - destruct Hvalid as [[Hside Hlt] | [Hside Hlt]].
    + exists (PhaseBidding chal resp bid def (atk :: hist) NeitherReady).
      constructor; assumption.
    + exists (PhaseBidding chal resp atk bid (def :: hist) NeitherReady).
      constructor; assumption.
  - destruct side.
    + destruct Hvalid as [Hready | Hready].
      * subst ready. exists (PhaseBidding chal resp atk def hist AttackerReady).
        constructor.
      * subst ready. exists (PhaseBidding chal resp atk def hist BothReady).
        constructor.
    + destruct Hvalid as [Hready | Hready].
      * subst ready. exists (PhaseBidding chal resp atk def hist DefenderReady).
        constructor.
      * subst ready. exists (PhaseBidding chal resp atk def hist BothReady).
        constructor.
  - subst ready. exists (PhaseAgreed chal resp atk def). constructor.
  - exists PhaseAborted. constructor.
Qed.

(** * Part X: Main Theorems and Examples *)

(** ** Section 10.1: Battle Outcomes *)

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

(** ** Section 10.2: Outcome Predicates *)

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

(** ** Section 10.3: Example Units and Forces

    Example units use realistic Clan warrior skill ratings:
    - Gunnery 2 / Piloting 1 = Total 3 (elite MechWarrior)
    - Gunnery 1 / Piloting 1 = Total 2 (legendary MechWarrior)
    - Gunnery 2 / Piloting 2 = Total 4 (borderline elite)
*)

Definition example_timberwolf : Unit :=
  mkUnit 1 OmniMech Heavy 75 2 1 true true.

Definition example_madcat : Unit :=
  mkUnit 2 OmniMech Heavy 75 1 1 true true.

Definition example_daishi : Unit :=
  mkUnit 3 OmniMech Assault 100 2 1 true true.

Definition example_summoner : Unit :=
  mkUnit 4 OmniMech Heavy 70 2 2 false true.

Definition example_elemental_point : Unit :=
  mkUnit 5 Elemental Light 5 1 1 true true.

Definition wolf_star : Force :=
  [example_timberwolf; example_madcat; example_summoner;
   example_summoner; example_elemental_point].

Definition falcon_binary : Force :=
  [example_daishi; example_daishi; example_timberwolf;
   example_madcat; example_summoner; example_summoner;
   example_elemental_point; example_elemental_point].

Lemma wolf_star_nonempty : wolf_star <> [].
Proof. unfold wolf_star. discriminate. Qed.

Lemma falcon_binary_nonempty : falcon_binary <> [].
Proof. unfold falcon_binary. discriminate. Qed.

Lemma wolf_star_metrics : force_metrics wolf_star = mkForceMetrics 5 295 3 5.
Proof. reflexivity. Qed.

Lemma falcon_binary_metrics : force_metrics falcon_binary = mkForceMetrics 8 500 6 8.
Proof. reflexivity. Qed.

(** ** Section 10.4: Example - Honorable Batchall Is Possible *)

Theorem honorable_batchall_possible :
  exists chal resp,
    chal_initial_force chal <> [] /\
    resp_force resp <> [] /\
    BatchallStep PhaseIdle (ActChallenge chal) (PhaseChallenged chal) /\
    BatchallStep (PhaseChallenged chal) (ActRespond resp) (PhaseResponded chal resp).
Proof.
  exists (mkBatchallChallenge
            (mkCommander 0 ClanWolf StarColonel true)
            (PrizeEnclave 1)
            wolf_star).
  exists (mkBatchallResponse
            (mkCommander 1 ClanJadeFalcon StarCaptain true)
            (LocEnclave 1)
            falcon_binary
            None).
  repeat split.
  - exact wolf_star_nonempty.
  - exact falcon_binary_nonempty.
  - constructor.
  - constructor.
Qed.

(** ** Section 10.4b: Example - Complete Batchall Negotiation

    This example demonstrates a complete batchall from challenge through
    agreement. Star Colonel Timur Malthus of Clan Jade Falcon challenges
    Star Captain Dwillt Radick of Clan Wolf for an enclave. Both sides
    pass, accepting the current bids. *)

Definition malthus : Commander :=
  mkCommander 100 ClanJadeFalcon StarColonel true.

Definition radick : Commander :=
  mkCommander 101 ClanWolf StarCaptain true.

Definition malthus_challenge : BatchallChallenge :=
  mkBatchallChallenge malthus (PrizeEnclave 42) falcon_binary.

Definition radick_response : BatchallResponse :=
  mkBatchallResponse radick (LocEnclave 42) wolf_star None.

Definition initial_falcon_bid : ForceBid :=
  mkForceBid Attacker falcon_binary malthus.

Definition initial_wolf_bid : ForceBid :=
  mkForceBid Defender wolf_star radick.

Example batchall_challenge_step :
  BatchallStep PhaseIdle
               (ActChallenge malthus_challenge)
               (PhaseChallenged malthus_challenge).
Proof. constructor. Qed.

Example batchall_response_step :
  BatchallStep (PhaseChallenged malthus_challenge)
               (ActRespond radick_response)
               (PhaseResponded malthus_challenge radick_response).
Proof. constructor. Qed.

Example batchall_start_bidding :
  BatchallStep (PhaseResponded malthus_challenge radick_response)
               (ActBid initial_falcon_bid)
               (PhaseBidding malthus_challenge radick_response
                             initial_falcon_bid initial_wolf_bid [] NeitherReady).
Proof. constructor. Qed.

Example batchall_attacker_passes :
  BatchallStep (PhaseBidding malthus_challenge radick_response
                             initial_falcon_bid initial_wolf_bid [] NeitherReady)
               (ActPass Attacker)
               (PhaseBidding malthus_challenge radick_response
                             initial_falcon_bid initial_wolf_bid [] AttackerReady).
Proof. constructor. Qed.

Example batchall_both_ready :
  BatchallStep (PhaseBidding malthus_challenge radick_response
                             initial_falcon_bid initial_wolf_bid [] AttackerReady)
               (ActPass Defender)
               (PhaseBidding malthus_challenge radick_response
                             initial_falcon_bid initial_wolf_bid [] BothReady).
Proof. constructor. Qed.

Example batchall_agreement :
  BatchallStep (PhaseBidding malthus_challenge radick_response
                             initial_falcon_bid initial_wolf_bid [] BothReady)
               ActClose
               (PhaseAgreed malthus_challenge radick_response
                           initial_falcon_bid initial_wolf_bid).
Proof. constructor. Qed.

Theorem complete_batchall_trace_exists :
  exists t : BatchallTrace PhaseIdle,
    trace_length t = 6.
Proof.
  exists (TraceCons batchall_challenge_step
         (TraceCons batchall_response_step
         (TraceCons batchall_start_bidding
         (TraceCons batchall_attacker_passes
         (TraceCons batchall_both_ready
         (TraceCons batchall_agreement
         (TraceNil _))))))).
  reflexivity.
Qed.

(** ** Section 10.4c: Example - Honorable Refusal

    A defender may refuse a challenge for valid reasons. Here, a defender
    refuses because the challenger lacks jurisdiction over the contested
    territory (e.g., it belongs to a different Clan). *)

Example refusal_for_jurisdiction :
  BatchallStep (PhaseChallenged malthus_challenge)
               (ActRefuse RefusalNoJurisdiction)
               (PhaseRefused malthus_challenge RefusalNoJurisdiction).
Proof. constructor. Qed.

Lemma refusal_no_jurisdiction_zero_honor :
  refusal_honor_delta RefusalNoJurisdiction = 0%Z.
Proof. reflexivity. Qed.

(** ** Section 10.4d: Example - Extended State with Safcon

    Demonstrates the extended protocol state tracking safcon. *)

Definition example_context : BattleContext :=
  standard_possession_context ClanWolf.

Example init_extended_has_active_safcon :
  let s := init_extended_state example_context in
  safcon_state_active (ext_safcon s) = true.
Proof. reflexivity. Qed.

Example extended_protocol_step :
  ExtendedStep (init_extended_state example_context)
               (EActProtocol (ActChallenge malthus_challenge))
               (mkExtendedState (PhaseChallenged malthus_challenge)
                               example_context
                               (init_safcon_state (ctx_safcon example_context))
                               ZellActive).
Proof. constructor. constructor. Qed.

Example time_passes_in_extended_state :
  let s := init_extended_state example_context in
  ExtendedStep s
               (EActTimeTick 24)
               (mkExtendedState (ext_phase s) (ext_context s)
                               (tick_safcon (ext_safcon s) 24) ZellActive).
Proof. constructor. Qed.

(** ** Section 10.5: Sublist Relation for Force Composition *)

Inductive Sublist {A : Type} : list A -> list A -> Prop :=
  | SublistNil : forall l, Sublist [] l
  | SublistSkip : forall x l1 l2, Sublist l1 l2 -> Sublist l1 (x :: l2)
  | SublistTake : forall x l1 l2, Sublist l1 l2 -> Sublist (x :: l1) (x :: l2).

Lemma sublist_nil : forall {A : Type} (l : list A), Sublist l [] -> l = [].
Proof. intros A l H. inversion H. reflexivity. Qed.

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

(** ** Section 10.5b: General SubForce Relation

    Unlike Sublist (which requires subsequence), SubForce allows
    arbitrary removal of units from any position. This better models
    real Clan bidding where a warrior might say "I bid away my Elementals"
    regardless of where they appear in the force roster. *)

Definition SubForce (f1 f2 : Force) : Prop :=
  forall u, In u f1 -> In u f2.

Lemma sublist_implies_subforce : forall f1 f2,
  Sublist f1 f2 -> SubForce f1 f2.
Proof.
  intros f1 f2 H.
  induction H as [l | x l1 l2 Hsub IH | x l1 l2 Hsub IH].
  - unfold SubForce. intros u Hin. inversion Hin.
  - unfold SubForce in *. intros u Hin. right. apply IH. exact Hin.
  - unfold SubForce in *. intros u Hin. destruct Hin as [Heq | Hin'].
    + left. exact Heq.
    + right. apply IH. exact Hin'.
Qed.

(** ** Section 10.5c: Minimum Viable Force and Cutdown

    A force has minimum viability when it can reasonably accomplish its
    mission. Bidding below this threshold (cutting down) is risky - the
    warrior may win the bidding but lose the battle.

    Minimum viability depends on context:
    - Total tonnage above a threshold
    - Unit count above a threshold
    - At least one unit of required class (e.g., assault for breaching) *)

Record ViabilityRequirements : Type := mkViabilityRequirements {
  min_tonnage : nat;
  min_units : nat;
  require_assault : bool
}.

Definition default_viability : ViabilityRequirements :=
  mkViabilityRequirements 100 2 false.

Definition has_assault_unit (f : Force) : bool :=
  existsb (fun u => match unit_weight u with Assault => true | _ => false end) f.

Definition force_meets_viability (f : Force) (req : ViabilityRequirements) : bool :=
  (min_tonnage req <=? fm_tonnage (force_metrics f)) &&
  (min_units req <=? fm_count (force_metrics f)) &&
  (negb (require_assault req) || has_assault_unit f).

Definition is_cutdown (original reduced : Force) (req : ViabilityRequirements) : Prop :=
  SubForce reduced original /\
  force_meets_viability original req = true /\
  force_meets_viability reduced req = false.

Lemma cutdown_reduces_metrics : forall original reduced req,
  Sublist reduced original ->
  is_cutdown original reduced req ->
  fm_le (force_metrics reduced) (force_metrics original).
Proof.
  intros original reduced req Hsub [_ _].
  apply sublist_metrics_le. exact Hsub.
Qed.

(** A valid bid never cuts below viability - this is dezgra (dishonorable). *)
Definition bid_respects_viability (bid : ForceBid) (req : ViabilityRequirements) : Prop :=
  force_meets_viability (bid_force bid) req = true.

(** ** Section 10.6: Internal Respects External *)

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

(** ** Section 10.7: Valid Bidding State Invariant *)

Definition valid_bidding_state (chal : BatchallChallenge) (resp : BatchallResponse)
                               (atk_bid def_bid : ForceBid) (hist : list ForceBid) : Prop :=
  bid_side atk_bid = Attacker /\
  bid_side def_bid = Defender /\
  fm_le (bid_metrics atk_bid) (force_metrics (chal_initial_force chal)) /\
  fm_le (bid_metrics def_bid) (force_metrics (resp_force resp)).

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

(** ** Section 10.8: Honor Integration with Protocol Traces *)

Open Scope Z_scope.

Definition action_actor (action : ProtocolAction) : option Commander :=
  match action with
  | ActChallenge chal => Some (chal_challenger chal)
  | ActRespond resp => Some (resp_defender resp)
  | ActBid bid => Some (bid_commander bid)
  | _ => None
  end.

Definition step_honor_delta (action : ProtocolAction) : Honor :=
  protocol_honor_delta action.

Fixpoint trace_honor_sum {phase : BatchallPhase} (t : BatchallTrace phase) : Honor :=
  match t with
  | TraceNil _ => 0
  | @TraceCons _ action _ _ rest => step_honor_delta action + trace_honor_sum rest
  end.

Definition initial_ledger : HonorLedger := empty_ledger.

Fixpoint apply_trace_honor {phase : BatchallPhase} (ledger : HonorLedger)
    (t : BatchallTrace phase) (default_actor : Commander) : HonorLedger :=
  match t with
  | TraceNil _ => ledger
  | @TraceCons _ action _ _ rest =>
      let actor := match action_actor action with
                   | Some c => c
                   | None => default_actor
                   end in
      let new_ledger := update_honor ledger actor (step_honor_delta action) in
      apply_trace_honor new_ledger rest default_actor
  end.

Lemma trace_honor_sum_nil : forall phase,
  trace_honor_sum (TraceNil phase) = 0.
Proof. reflexivity. Qed.

Lemma trace_honor_sum_cons : forall phase1 action phase2 step rest,
  trace_honor_sum (@TraceCons phase1 action phase2 step rest) =
  step_honor_delta action + trace_honor_sum rest.
Proof. reflexivity. Qed.

Lemma challenge_honor_positive : forall chal,
  step_honor_delta (ActChallenge chal) = 1.
Proof. reflexivity. Qed.

Lemma respond_honor_positive : forall resp,
  step_honor_delta (ActRespond resp) = 1.
Proof. reflexivity. Qed.

Lemma withdraw_honor_negative : forall side,
  step_honor_delta (ActWithdraw side) = -2.
Proof. reflexivity. Qed.

Lemma break_bid_severely_negative :
  step_honor_delta ActBreakBid = -10.
Proof. reflexivity. Qed.

Theorem honorable_conclusion_positive_trace : forall chal resp,
  let t := TraceCons (StepChallenge chal)
           (TraceCons (StepRespond chal resp)
           (TraceNil (PhaseResponded chal resp))) in
  trace_honor_sum t = 2.
Proof.
  intros chal resp. simpl. reflexivity.
Qed.

Close Scope Z_scope.

(** ** Section 10.9: Internal-External Bidding Integration *)

Record FullBatchallResult : Type := mkFullBatchallResult {
  fbr_external : ExternalResult;
  fbr_attacker_internal : option InternalResult;
  fbr_defender_internal : option InternalResult
}.

Definition attacker_final_force (result : FullBatchallResult) : Force :=
  match fbr_attacker_internal result with
  | Some int_res => icand_force (int_winner int_res)
  | None => bid_force (ext_attacker_bid (fbr_external result))
  end.

Definition defender_final_force (result : FullBatchallResult) : Force :=
  match fbr_defender_internal result with
  | Some int_res => icand_force (int_winner int_res)
  | None => bid_force (ext_defender_bid (fbr_external result))
  end.

Definition internal_result_valid (int_res : InternalResult) (max_force : Force) : Prop :=
  Sublist (icand_force (int_winner int_res)) max_force.

Definition full_result_valid (result : FullBatchallResult) : Prop :=
  (forall int_res, fbr_attacker_internal result = Some int_res ->
    internal_result_valid int_res (bid_force (ext_attacker_bid (fbr_external result)))) /\
  (forall int_res, fbr_defender_internal result = Some int_res ->
    internal_result_valid int_res (bid_force (ext_defender_bid (fbr_external result)))).

Theorem full_result_forces_bounded : forall result,
  full_result_valid result ->
  fm_le (force_metrics (attacker_final_force result))
        (bid_metrics (ext_attacker_bid (fbr_external result))) /\
  fm_le (force_metrics (defender_final_force result))
        (bid_metrics (ext_defender_bid (fbr_external result))).
Proof.
  intros result [Hatk Hdef].
  split.
  - unfold attacker_final_force.
    destruct (fbr_attacker_internal result) as [int_res|] eqn:Heq.
    + specialize (Hatk int_res eq_refl).
      unfold internal_result_valid in Hatk.
      apply sublist_metrics_le. exact Hatk.
    + unfold bid_metrics. apply fm_le_refl.
  - unfold defender_final_force.
    destruct (fbr_defender_internal result) as [int_res|] eqn:Heq.
    + specialize (Hdef int_res eq_refl).
      unfold internal_result_valid in Hdef.
      apply sublist_metrics_le. exact Hdef.
    + unfold bid_metrics. apply fm_le_refl.
Qed.

(** ** Section 10.10: Sublist Connection to Bidding *)

Definition bid_reduces_force (bid1 bid2 : ForceBid) : Prop :=
  bid_side bid1 = bid_side bid2 /\
  Sublist (bid_force bid1) (bid_force bid2).

Lemma bid_reduces_implies_metrics_le : forall bid1 bid2,
  bid_reduces_force bid1 bid2 ->
  fm_le (bid_metrics bid1) (bid_metrics bid2).
Proof.
  intros bid1 bid2 [Hside Hsub].
  unfold bid_metrics.
  apply sublist_metrics_le. exact Hsub.
Qed.

Lemma sublist_refl : forall {A : Type} (l : list A), Sublist l l.
Proof.
  induction l as [|x rest IH].
  - constructor.
  - apply SublistTake. exact IH.
Qed.

Lemma sublist_trans : forall {A : Type} (l1 l2 l3 : list A),
  Sublist l1 l2 -> Sublist l2 l3 -> Sublist l1 l3.
Proof.
  intros A l1 l2 l3 H12 H23.
  revert l1 H12.
  induction H23 as [l | x l2' l3' H23 IH | x l2' l3' H23 IH]; intros l1 H12.
  - apply sublist_nil in H12. subst. constructor.
  - apply SublistSkip. apply IH. exact H12.
  - inversion H12; subst.
    + constructor.
    + apply SublistSkip. apply IH. exact H1.
    + apply SublistTake. apply IH. exact H1.
Qed.

Theorem bid_chain_valid : forall b1 b2 b3,
  bid_reduces_force b1 b2 ->
  bid_reduces_force b2 b3 ->
  bid_reduces_force b1 b3.
Proof.
  intros b1 b2 b3 [Hs12 Hsub12] [Hs23 Hsub23].
  split.
  - congruence.
  - apply sublist_trans with (l2 := bid_force b2); assumption.
Qed.
