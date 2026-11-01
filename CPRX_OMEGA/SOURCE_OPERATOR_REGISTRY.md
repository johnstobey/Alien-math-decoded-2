# Source operator registry — observed and reconstructed, not forty-eight assigned operators

Source pages accessed via web retrieval; exact original HTML bytes unavailable to local executor. Line ranges reference web-rendered pages. The registry covers the explicit mathematical families found in inspected passages; it does not claim exhaustive semantic extraction of all 24 lessons.

## OP01: T
Lesson 1, lines 74-78. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.01.html)

- Passage relationship: equal twelve sectors
- Formalization: `x -> x+1 mod 12`
- Attribution status: inferred from explicit geometry
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP02: E
Lesson 1, lines 106-113. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.01.html)

- Passage relationship: triplicities separated by 120 degrees
- Formalization: `x -> x+4 mod 12`
- Attribution status: direct angular transformation
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP03: element
Lesson 1, lines 106-113. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.01.html)

- Passage relationship: element partition of twelve signs
- Formalization: `x mod 4`
- Attribution status: inferred partition indexing
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP04: modality
Lesson 1, lines 106-113. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.01.html)

- Passage relationship: three modality positions per element
- Formalization: `x mod 3`
- Attribution status: inferred partition indexing
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP05: D0
Lesson 9, lines 82-97. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.09.html)

- Passage relationship: conjunction 0 degrees
- Formalization: `x -> x+0 mod 12`
- Attribution status: direct aspect
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP06: D1
Lesson 9, lines 82-97. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.09.html)

- Passage relationship: semisextile 30 degrees
- Formalization: `x -> x+1 mod 12`
- Attribution status: direct aspect
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP07: D2
Lesson 9, lines 82-97. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.09.html)

- Passage relationship: sextile 60 degrees
- Formalization: `x -> x+2 mod 12`
- Attribution status: direct aspect
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP08: D3
Lesson 9, lines 82-97. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.09.html)

- Passage relationship: square 90 degrees
- Formalization: `x -> x+3 mod 12`
- Attribution status: direct aspect
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP09: D4
Lesson 9, lines 82-97. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.09.html)

- Passage relationship: trine 120 degrees
- Formalization: `x -> x+4 mod 12`
- Attribution status: direct aspect
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP10: D5
Lesson 9, lines 82-97. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.09.html)

- Passage relationship: quincunx 150 degrees
- Formalization: `x -> x+5 mod 12`
- Attribution status: direct aspect
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP11: D6
Lesson 9, lines 82-97. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.09.html)

- Passage relationship: opposition 180 degrees
- Formalization: `x -> x+6 mod 12`
- Attribution status: direct aspect
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP12: q
Lesson 9, lines 82-97. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.09.html)

- Passage relationship: aspect distance considered undirected
- Formalization: `d -> min(d, 12-d)`
- Attribution status: inferred reflection quotient
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP13: time_partition
Lesson 4, lines 109-129. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.04.html)

- Passage relationship: water/earth past, fire/air future
- Formalization: `x mod 4 in {1,3} = past; else future`
- Attribution status: direct classification formalized
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP14: aspect_time
Lesson 9, lines 152-193. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.09.html)

- Passage relationship: alternating past and future aspect classes
- Formalization: `d parity and aspect class`
- Attribution status: direct classification formalized
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP15: progression
Lesson 18, lines 14-17. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.18.html)

- Passage relationship: progressions link one day to one year
- Formalization: `t_year <-> t_day`
- Attribution status: hypothesis; numeric operator underdetermined
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP16: plane_change
Lesson 18, lines 32-44. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.18.html)

- Passage relationship: rotation/revolution and projection between planes
- Formalization: `requires explicit coordinate conversion`
- Attribution status: hypothesis; no map specified
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP17: permutation_count
Lesson 8, lines 74-81. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.08.html)

- Passage relationship: arrangement enumeration and likelihood model
- Formalization: `factorial(6)=720`
- Attribution status: explicit counting; probability model contingent
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP18: representation
Lesson 1, lines 23-28. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.01.html)

- Passage relationship: abstract relations independent of causal physical effects
- Formalization: `formal correspondence across domains unspecified`
- Attribution status: interpretive principle
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP19: I
Lesson 9, lines 82-97. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.09.html)

- Passage relationship: reflection of aspect displacement d and -d
- Formalization: `x -> -x mod 12`
- Attribution status: reconstructed, not verbatim operator
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP20: rho
Lesson 9, lines 82-97. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.09.html)

- Passage relationship: reflection offset by one sector
- Formalization: `x -> 11-x mod 12`
- Attribution status: engineered RAP-12; not course asserted
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP21: A
Lesson 1, lines 74-78. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.01.html)

- Passage relationship: antipodal reflection opposite sector
- Formalization: `x -> x+6 mod 12`
- Attribution status: deduced from aspect opposition
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.

## OP22: cyclic
Lesson 1, lines 74-78. [Source](https://www.bonniehill.net/pages.aux/astrology/tobey/tobey.01.html)

- Passage relationship: 360-degree circle closure
- Formalization: `x -> x+12 = x`
- Attribution status: deduced finite ring relation
- Domain: Z/12Z when indexed, otherwise stated counting/semantic domain.
