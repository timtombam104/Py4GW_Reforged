from __future__ import annotations

import re
import time

from Py4GWCoreLib import GLOBAL_CACHE, BuildMgr, Effects, Player, Profession, Routines
from Py4GWCoreLib.BuildMgr import BuildCoroutine
from Py4GWCoreLib.Builds.Any.HeroAI import HeroAI_Build
from Py4GWCoreLib.HeroAI.types import Skilltarget, SkillType
from Py4GWCoreLib.Skill import Skill

PIOUS_RENEWAL_ID = Skill.GetID("Pious_Renewal")

# A teardown skill spends one of YOUR Dervish enchantments. The skill text says
# so ("remove 1 Dervish enchantment", "lose 1 ...", "removes a ..."), which also
# covers every PvP variant. The lookbehinds skip reactive wording such as Aura of
# Holy Might ("whenever you lose a Dervish enchantment"). Checked against the
# repo's skill_descriptions.json: it matches exactly the Guild Wars wiki's
# Teardown list and nothing else.
TEARDOWN_TEXT = re.compile(
    r"(?<!whenever you )(?<!when you )\b(?:remov(?:e|es)|los(?:e|es))\s+(?:1|one|an?)"
    r"\s+(?:of\s+your\s+)?dervish\s+enchantments?",
    re.IGNORECASE,
)

# How long Pious Renewal waits for your other enchantments to be cast first.
PIOUS_RENEWAL_HOLD_MAX_MS = 2500
# The client sees effect changes a little after the server applies them. After a
# teardown skill or another enchantment is cast, teardown skills stay blocked
# until the effect list visibly changes, or this long at most.
PENDING_EFFECT_LOCK_MAX_MS = 1000

DEBUG_LOG = False


class DervPiousRenewalTeardown(BuildMgr):
    """
    Makes Pious Renewal the only enchantment that Dervish teardown skills spend,
    for any Dervish-primary skill bar that carries Pious Renewal.

    The game always removes the MOST RECENTLY applied Dervish enchantment when a
    teardown skill fires, so this build enforces two things:

      1. Gate: every equipped teardown skill is hidden from the HeroAI fallback
         unless Pious Renewal is the newest Dervish enchantment. HeroAI still
         chooses targets and timing, so any teardown skill works unchanged.
      2. Order: Pious Renewal is cast by this build, and only after your other
         self-cast enchantments are up (waiting at most
         PIOUS_RENEWAL_HOLD_MAX_MS), so it ends up the newest.

    If something newer than Pious Renewal appears, the gate stays closed until
    Pious Renewal ends (8 seconds) and the cycle restarts. Pious Renewal
    recharges itself when it ends, including when a teardown skill removes it.

    Matching: this build scores 1 (the lowest positive score), so any more
    specific build for a given bar still wins over it.

    The gate also applies out of combat. Pious Renewal itself is only cast in or
    near combat.
    """

    def __init__(self, match_only: bool = False):
        super().__init__(
            name="Pious Renewal Teardown",
            required_primary=Profession.Dervish,
            template_code="OgejkyrG7SbXSXRXPXihcXyg4OA",
            required_skills=[PIOUS_RENEWAL_ID],
        )
        if match_only:
            return

        self._is_teardown_cache: dict[int, bool] = {}
        self._is_dervish_enchantment_cache: dict[int, bool] = {}
        self._watched_ready: dict[int, bool] = {}
        self._lock_until_ms = 0.0
        self._lock_signature: frozenset[int] = frozenset()
        self._hold_since_ms = 0.0
        self._gate_open = False

        # Skills that are not blocked this tick are still cast by HeroAI.
        self.SetFallback("HeroAI", HeroAI_Build(standalone_fallback=True))
        self.SetSkillCastingFn(self._run_local_skill_logic)

    # region classification
    def _is_teardown_skill(self, skill_id: int) -> bool:
        cached = self._is_teardown_cache.get(skill_id)
        if cached is None:
            text = f"{Skill.GetConciseDescription(skill_id)} || {Skill.GetDescription(skill_id)}"
            cached = bool(TEARDOWN_TEXT.search(text))
            self._is_teardown_cache[skill_id] = cached
        return cached

    def _is_dervish_enchantment(self, skill_id: int) -> bool:
        cached = self._is_dervish_enchantment_cache.get(skill_id)
        if cached is None:
            _, skill_type_name = GLOBAL_CACHE.Skill.GetType(skill_id)
            _, profession_name = GLOBAL_CACHE.Skill.GetProfession(skill_id)
            # Flash enchantments say "Enchantment Spell" in their text, so they
            # count even if the type lookup reports something else.
            is_enchantment = skill_type_name == "Enchantment" or (
                "enchantment spell" in Skill.GetConciseDescription(skill_id).lower()
            )
            cached = is_enchantment and profession_name == "Dervish"
            self._is_dervish_enchantment_cache[skill_id] = cached
        return cached

    def _is_self_maintain_enchantment(self, skill_id: int) -> bool:
        """A plain self-cast enchantment that HeroAI keeps up without special conditions."""
        if not self._is_dervish_enchantment(skill_id):
            return False
        custom_skill = self.GetCustomSkill(skill_id)
        if not custom_skill:
            return False
        if custom_skill.SkillType != SkillType.Enchantment.value:
            return False
        if custom_skill.TargetAllegiance != Skilltarget.Self.value:
            return False
        conditions = custom_skill.Conditions
        return not (
            conditions.IsOutOfCombat
            or conditions.LessLife
            or conditions.MoreLife
            or conditions.HasEnchantment
            or conditions.HasDervishEnchantment
        )
    # endregion

    # region effect state
    def _dervish_enchantment_ages(self) -> dict[int, int]:
        """Active Dervish enchantments on the player mapped to time since applied."""
        ages: dict[int, int] = {}
        for effect in Effects.GetEffects(Player.GetAgentID()):
            skill_id = int(effect.skill_id)
            if self._is_dervish_enchantment(skill_id):
                ages[skill_id] = int(effect.time_elapsed)
        return ages

    @staticmethod
    def _feeder_is_newest(ages: dict[int, int]) -> bool:
        """True only when Pious Renewal is strictly the newest Dervish enchantment.

        A tie counts as not newest, which errs on the side of blocking.
        """
        feeder_age = ages.get(PIOUS_RENEWAL_ID)
        if feeder_age is None:
            return False
        return all(feeder_age < age for skill_id, age in ages.items() if skill_id != PIOUS_RENEWAL_ID)

    def _update_pending_effect_lock(self, bar: list[int], ages: dict[int, int], now_ms: float) -> bool:
        """Keep the gate closed while a just-cast skill has not shown up in the effect list yet."""
        watched = [
            skill_id
            for skill_id in bar
            if skill_id != PIOUS_RENEWAL_ID
            and (self._is_teardown_skill(skill_id) or self._is_dervish_enchantment(skill_id))
        ]
        ready_now = {skill_id: bool(Routines.Checks.Skills.IsSkillIDReady(skill_id)) for skill_id in watched}
        just_cast = any(
            self._watched_ready.get(skill_id, False) and not is_ready for skill_id, is_ready in ready_now.items()
        )
        self._watched_ready = ready_now

        signature = frozenset(ages)
        if just_cast:
            self._lock_until_ms = now_ms + PENDING_EFFECT_LOCK_MAX_MS
            self._lock_signature = signature
        elif self._lock_until_ms and signature != self._lock_signature:
            self._lock_until_ms = 0.0  # the effect list caught up with the server
        if self._lock_until_ms and now_ms >= self._lock_until_ms:
            self._lock_until_ms = 0.0
        return self._lock_until_ms > 0.0

    def _should_hold_feeder(self, bar: list[int], ages: dict[int, int], now_ms: float) -> bool:
        """Wait for other self-cast enchantments HeroAI is about to cast, so Pious Renewal lands last."""
        pending = [
            skill_id
            for skill_id in bar
            if skill_id != PIOUS_RENEWAL_ID
            and skill_id not in ages
            and self._is_self_maintain_enchantment(skill_id)
            and self.CanCastSkillID(skill_id)
        ]
        if not pending:
            self._hold_since_ms = 0.0
            return False
        if not self._hold_since_ms:
            self._hold_since_ms = now_ms
        return now_ms - self._hold_since_ms < PIOUS_RENEWAL_HOLD_MAX_MS
    # endregion

    def _reset_state(self) -> None:
        self._watched_ready = {}
        self._lock_until_ms = 0.0
        self._hold_since_ms = 0.0
        self._gate_open = False

    def _run_local_skill_logic(self) -> BuildCoroutine:
        bar = [int(skill_id) for skill_id in self._get_current_skills()]
        if PIOUS_RENEWAL_ID not in bar:
            self.SetBlockedSkills([])
            self._reset_state()
            return False

        now_ms = time.monotonic() * 1000.0
        ages = self._dervish_enchantment_ages()
        locked = self._update_pending_effect_lock(bar, ages, now_ms)

        gate_open = PIOUS_RENEWAL_ID in ages and self._feeder_is_newest(ages) and not locked
        blocked = [PIOUS_RENEWAL_ID]
        if not gate_open:
            blocked += [skill_id for skill_id in bar if self._is_teardown_skill(skill_id)]
        self.SetBlockedSkills(blocked)

        if DEBUG_LOG and gate_open != self._gate_open:
            self._debug(f"teardown gate {'OPEN' if gate_open else 'closed'} ages={ages} locked={locked}")
        self._gate_open = gate_open

        if not (self.IsInAggro() or self.IsCloseToAggro()):
            return False
        if PIOUS_RENEWAL_ID in ages:
            self._hold_since_ms = 0.0
            return False
        if self._should_hold_feeder(bar, ages, now_ms):
            return False

        return (yield from self.CastSkillID(skill_id=PIOUS_RENEWAL_ID, log=False, aftercast_delay=250))
