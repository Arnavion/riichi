> This is a translation of https://note.com/yuarasino/n/n1ba95bf3b618 where the author defines the "Extended MPSZ" notation. This notation is used in this crate for representing tiles, melds and hands.
> 
> The original text is Copyright Arashino Yuu (2023).
> 
> This crate does not support parsing the river, only hands, so the section about representing the river is not relevant.

# A proposal for extending MPSZ notation used in Riichi Mahjong


## Introduction

There are two notations used for Riichi Mahjong tiles.

The first method that is used for written game logs uses:

- `一` - `九` (1-9 in kanji) for manzu (character tiles).
- `①` - `⑨` (1-9 in circles) for pinzu (dot tiles).
- `１` - `９` (1-9 in Indo-Arabic numerals) for souzu (bamboo tiles).
- `T` (ton, East wind), `N` (nan, South wind), `西` (shaa, West wind) and `北` (pei, North wind) for wind tiles.
- `白` (haku, White dragon), `R` (hatsu, ryuufa, Green dragon) and `中` (chun, Red dragon) for dragon tiles.

The second is the MPSZ notation that uses:

- `1m` - `9m` for manzu.
- `1p` - `9p` for pinzu.
- `1s` - `9s` for souzu.
- `1z` - `7z` for jihai (honor tiles).

However there is no standard way to represent open hand melds or the river (pond, list of a player's discards), so these are usually represented via ad-hoc methods like parentheticals. While such ad-hoc methods are fine for discussing informally such as on social media, as a programmer I would like a format that:

- ... everyone agrees to use, so that it is possible to create interoperable tools.
- ... is easy to parse programmatically and also easy to share as text.
- ... is easy to read and write for people.

Therefore I propose a notation that extends the existing MPSZ notation to represent open melds and discards.


## Representing hand tiles

### Suits

- `m` for manzu.
- `p` for pinzu.
- `s` for souzu.
- `z` for jihai.
- `x` for face-down or unknown tiles, eg arbitrary tiles needed for some demonstration.

### Values

- `1` - `9` for manzu, pinzu and souzu to represent their values directly.
- `0` for akadora (red five tiles).
- `1` - `7` for jihai, in the order ton, nan, shaa, pei, haku, hatsu, chun.
- Face-down or unknown tiles can have arbitrary numerical values.

### Multiple tiles

For a continuous run of tiles in the same suit, the suit indicator does not need to be written after every number. It can be written just once, after the final tile in the run.

A tile that is added to a hand via draw or by calling tsumo or ron should be written separately from the hand. For example, a run `3456s` along with a `3s` that was just drawn would be written as `3456s3s`.

When writing in Japanese, where words don't already have spaces around them, it would be good to put a space after the run so that it is easier to read.

### Examples

- Manzu: `1m`, `123m`
- Pinzu: `2p`, `555p`
- Souzu: `3s`, `444s`
- Akadora: `0m`, `0p`, `0s`
- Jihai: `1z`, `222z`
- Face-down tiles: `0x`, `0011x`
- Combined: `2234m345p345s111z 5z`
- A shanpon wait with hatsu and some unknown tile: `00x66z`


## Representing open hand melds

A single open hand meld is just like a run of tiles that make up the meld. The type of meld is represented thusly:

- `-` for a minjun (open sequence formed by calling chii), a minkou (open triplet formed by calling pon), and a daiminkan (big open quad formed by calling kan to add a fourth tile from another player's discard to an ankou [triplet of tiles in the closed part of the hand]). The mnemonic is that the added tile was missing from the meld that it now belongs to.
- `=` for a shouminkan (small open quad formed by calling kan to add a fourth tile to a minkou). The mnemonic is that the added tile rests horizontally on top of the originally pon'd tile.
- `+` for an ankan (closed quad formed by calling kan on four tiles in the closed part of the hand). The mnemonic is that the call increases the value of the hand.

The position of the called tile and marker represents which tile was called and which player it was called from:

- When the tile is called from kamicha (left player), the called tile is made to be the first tile in the run, and the marker is placed after it.
- When the tile is called from toimen (across player), the called tile is made to be the second tile in the run, and the marker is placed after it.
- When the tile is called from shimocha (right player), the called tile is made to be the third tile in the run, and the marker is placed after it, but before the suit indicator.
- For an ankan, the last drawn tile is made to be the fourth tile in the run, and the marker is placed after it, but before the suit indicator.
- For a shouminkan, the last drawn tile is made to be the fourth tile in the run, and the minkou marker is changed into the shouminkan marker.

### Examples

- Chii: `2-13m`
- Pon: `55-5p`
- Daiminkan: `444-4s`
- Shouminkan: `55=50p`
- Ankan: `1111+z`
- Combined: `2245m5z 4-35s 0-34p 11=11z`


## Representing the river

The river is represented as a sequence of discarded tiles. Markers are used to describe the manner in which the tile was discarded:

- `=` for a tile that was discarded by tsumogiri (drawn tile was immediately discarded). The mnemonic is that the it reminds one of the kana ツ (tsu) of tsumo.
- `+` for a tile that was discarded as part of calling riichi. The mnemonic is that the call increases the value of the hand.
- `-` for a tile that is called by another player. The mnemonic is that the tile has been removed from the player's river.

The marker is placed before the suit indicator. If multiple markers apply to the same tile, they can be written consecutively.

### Examples

- Tsumogiri: `3=m`
- Riichi: `5+p`
- Tile called by another player: `4-s`
- Combined: `1=p3z5-s0+-m4=m1=z 5=-z7=p8=m`


## Examples of actual game states

- Image 1

  ![Image 1](https://assets.st-note.com/img/1677797367168-tQZEbygzjX.png)

  Dora indicators: `0p`

  Hand: `22256p55s6z 6-57m 111-z`

  River: `4z2z1s9m2=m5=z 3=z7s8=m7m`

- Image 2

  ![Image 2](https://assets.st-note.com/img/1677798203369-sF1uU6Sb1W.png)

  Dora indicators: `1p`

  Hand: `23468p11345678s 2z`

  River: `4z1=m7+-m3=s`

I realize the river representation appears messy, but it's relatively straightforward to transcribe it from an image. Even without prior knowledge, I believe it is sufficient to immediately impart information like "this tile was pon'd" or "this tile was cut via tsumogiri".


## Conclusion

If you have any suggestions for this notation or find any situations that it cannot represent, please comment on this blog post or reach out to me on Twitter!

I am planning to make a Mahjong tool myself and will use this notation in that. I hope it will be a useful tool for all Mahjong players, so I appreciate your support in this venture!
