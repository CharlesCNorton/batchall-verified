```
                    ╔═══════════════════════════════════════════════════════════════╗
                    ║                                                               ║
                    ║  ┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓  ║
                    ║  ┃                                                         ┃  ║
                    ║  ┃                ░▒▓█  THE BATCHALL  █▓▒░                 ┃  ║
                    ║  ┃                      ═══════════                        ┃  ║
                    ║  ┃                                                         ┃  ║
                    ║  ┃        A   F O R M A L   V E R I F I C A T I O N        ┃  ║
                    ║  ┃                                                         ┃  ║
                    ║  ┃              ◆  IN THE COQ PROOF ASSISTANT  ◆          ┃  ║
                    ║  ┃                                                         ┃  ║
                    ║  ┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛  ║
                    ║                                                               ║
                    ║          ┌─────────────────────────────────────────┐          ║
                    ║          │  Machine-checked formalization of the   │          ║
                    ║          │  Clan ritual of challenge. The state    │          ║
                    ║          │  machine of honor. The well-foundedness │          ║
                    ║          │  of bidding. The certainty that all     │          ║
                    ║          │  challenges must conclude.              │          ║
                    ║          └─────────────────────────────────────────┘          ║
                    ║                                                               ║
                    ║                 ✦  Charles C. Norton  ✦                      ║
                    ║                                                               ║
                    ║                        ═══════ ◈ ═══════                      ║
                    ║                                                               ║
                    ║           "The Clans are a covenant, bound not by             ║
                    ║            blood alone but by the sacred forms that           ║
                    ║            give our blood meaning."                           ║
                    ║                                                               ║
                    ║                    — Nicholas Kerensky                        ║
                    ║                      Founding of the Clans, 2815              ║
                    ║                                                               ║
                    ║                        ═══════ ◈ ═══════                      ║
                    ║                                                               ║
                    ║   ┌───────────────────────────────────────────────────────┐   ║
                    ║   │                                                       │   ║
                    ║   │   PROVENANCE                                          │   ║
                    ║   │   ══════════                                          │   ║
                    ║   │   Author .............. Charles C. Norton             │   ║
                    ║   │   Caste ............... Scientist (Seeker of Proofs)  │   ║
                    ║   │   Affiliation ......... Clan Goliath Scorpion         │   ║
                    ║   │   Date ................ December 2025                 │   ║
                    ║   │                                                       │   ║
                    ║   └───────────────────────────────────────────────────────┘   ║
                    ║                                                               ║
                    ╠═══════════════════════════════════════════════════════════════╣
                    ║                                                               ║
                    ║                    ☩  SEYLA  ☩                               ║
                    ║                                                               ║
                    ╚═══════════════════════════════════════════════════════════════╝
```

---

## The Remembrance

This repository contains a **machine-verified formalization** of the Clan batchall—the ritual of challenge that governs honorable warfare among the Clans of Kerensky. The formalization is written in the **Coq proof assistant** and verifies the fundamental properties that make the batchall a valid ritual:

- **Termination**: All batchalls must conclude. Bidding cannot continue forever.
- **Determinism**: Given a state and action, at most one next state exists.
- **Progress**: From every non-terminal state, valid actions exist.
- **Honor Accounting**: Every action carries verified honor consequences.

---

## Structure of the Codex

The formalization is organized into three books, following the structure of a Clan Remembrance:

### Book I: The Warriors
> *Of Clans and their children. Of ranks earned in Trials. Of warriors and war machines. Of the measure of force.*

- Enumeration of the sixteen Clans of the Invasion Era
- The rank structure from Warrior to Khan
- Unit classifications (OmniMech, BattleMech, Elemental, etc.)
- The Kerensky Combat Rating (KCR) system
- Force metrics and the partial order on forces

### Book II: The Codes
> *Of honor, the currency of the Clans. Of Zellbrigen, the duel-law. Of Safcon and Hegira. Of Trials that determine all.*

- The seven Trial types (Position, Possession, Refusal, Grievance, Bloodright, Abjuration, Annihilation)
- Zellbrigen: the honor code of combat
- Safcon: safe conduct for transports
- Hegira: the right of honorable retreat
- The honor ledger system

### Book III: The Batchall
> *Of the ritual of challenge. Of bid and counterbid. Of the certainty that all contests must conclude. "Bargained well and done."*

- The batchall state machine (Idle → Challenged → Responded → Bidding → Agreed)
- Coalition support for multi-Clan alliances
- Protocol actions and transitions
- The central termination theorems

---

## Verification

### Requirements

- **Coq 8.19** (tested with Coq Platform 8.19~2024.10)

### Compilation

```bash
coqc batchall.v
```

The file compiles with only benign warnings about comment formatting. All proofs are accepted.

### Key Theorems

| Theorem | Statement |
|---------|-----------|
| `fm_lt_well_founded` | The strict order on force metrics is well-founded |
| `batchall_bid_well_founded` | The bid ordering is well-founded |
| `protocol_determinism` | State transitions are deterministic |
| `non_terminal_can_progress` | Non-terminal states always have valid actions |
| `batchall_termination_strong` | The batchall protocol terminates |
| `annihilation_forbids_withdrawal` | Context validation (no hegira in Annihilation) |

---

## The Telling: An Example

The formalization includes a complete verified example: **Star Colonel Timur Malthus** of Clan Jade Falcon challenges **Star Captain Radick** of Clan Wolf for an enclave on Twycross.

```coq
Example step1_challenge :
  BatchallStep PhaseIdle (ActChallenge malthus_challenge) phase_after_challenge.
Proof. constructor. Qed.

Example step6_close :
  BatchallStep phase_after_def_pass ActClose phase_agreed.
Proof. apply StepClose. Qed.
```

The trace proceeds: Challenge → Response → Initial Bid → Attacker Pass → Defender Pass → Close.

*"Bargained well and done."*

---

## License

MIT License. See [LICENSE](LICENSE).

---

```
                              ╭─────────────────────╮
                              │                     │
                              │   So ends this      │
                              │   Remembrance.      │
                              │                     │
                              │   Let it be         │
                              │   verified.         │
                              │                     │
                              │   Let it be true.   │
                              │                     │
                              │       ☩ SEYLA ☩     │
                              │                     │
                              ╰─────────────────────╯
```
