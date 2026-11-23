HAI
  WAZZUP
    I HAS A temp ITZ 38
  BUHBYE

  BTW Else-if ladder classifying temperature across all branches
  BTW Branch 1 -> YA RLY (freezing <= 0)
  temp R -5
  BOTH SAEM temp AN SMALLR OF temp AN 0
  O RLY?
    YA RLY
      VISIBLE temp + "C -> Freezing"
    MEBBE BOTH SAEM temp AN SMALLR OF temp AN 15
      VISIBLE temp + "C -> Cold"
    MEBBE BOTH SAEM temp AN SMALLR OF temp AN 28
      VISIBLE temp + "C -> Warm"
    NO WAI
      VISIBLE temp + "C -> Hot"
  OIC

  BTW Branch 2 -> first else-if (cold <= 15)
  temp R 12
  BOTH SAEM temp AN SMALLR OF temp AN 0
  O RLY?
    YA RLY
      VISIBLE temp + "C -> Freezing"
    MEBBE BOTH SAEM temp AN SMALLR OF temp AN 15
      VISIBLE temp + "C -> Cold"
    MEBBE BOTH SAEM temp AN SMALLR OF temp AN 28
      VISIBLE temp + "C -> Warm"
    NO WAI
      VISIBLE temp + "C -> Hot"
  OIC

  BTW Branch 3 -> second else-if (warm <= 28)
  temp R 24
  BOTH SAEM temp AN SMALLR OF temp AN 0
  O RLY?
    YA RLY
      VISIBLE temp + "C -> Freezing"
    MEBBE BOTH SAEM temp AN SMALLR OF temp AN 15
      VISIBLE temp + "C -> Cold"
    MEBBE BOTH SAEM temp AN SMALLR OF temp AN 28
      VISIBLE temp + "C -> Warm"
    NO WAI
      VISIBLE temp + "C -> Hot"
  OIC

  BTW Branch 4 -> else (hot > 28)
  temp R 38
  BOTH SAEM temp AN SMALLR OF temp AN 0
  O RLY?
    YA RLY
      VISIBLE temp + "C -> Freezing"
    MEBBE BOTH SAEM temp AN SMALLR OF temp AN 15
      VISIBLE temp + "C -> Cold"
    MEBBE BOTH SAEM temp AN SMALLR OF temp AN 28
      VISIBLE temp + "C -> Warm"
    NO WAI
      VISIBLE temp + "C -> Hot"
  OIC
KTHXBYE
