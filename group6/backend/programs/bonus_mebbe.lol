HAI
  WAZZUP
    I HAS A score ITZ 85
    I HAS A flag ITZ FAIL
  BUHBYE

  BTW 1) MEBBE short-circuits after the first matching branch
  BOTH SAEM score AN BIGGR OF score AN 90
  O RLY?
    YA RLY
      VISIBLE "Case 1 -> YA RLY (90+)"
    MEBBE BOTH SAEM score AN BIGGR OF score AN 80
      VISIBLE "Case 1 -> first MEBBE (80+)"
    MEBBE BOTH SAEM score AN BIGGR OF score AN 70
      VISIBLE "Case 1 -> second MEBBE (should NOT run)"
    NO WAI
      VISIBLE "Case 1 -> NO WAI"
  OIC

  BTW 2) MEBBE with boolean expression and no NO WAI clause
  flag
  O RLY?
    YA RLY
      VISIBLE "Case 2 -> YA RLY"
    MEBBE BOTH OF DIFFRINT score AN 0 AN BOTH SAEM score AN 85
      VISIBLE "Case 2 -> MEBBE boolean condition matched"
  OIC

  BTW 3) MEBBE chain where none match (no NO WAI)
  score R 10
  BOTH SAEM score AN 100
  O RLY?
    YA RLY
      VISIBLE "Case 3 -> 100"
    MEBBE BOTH SAEM score AN 50
      VISIBLE "Case 3 -> 50"
  OIC

  VISIBLE "MEBBE test complete"
KTHXBYE
