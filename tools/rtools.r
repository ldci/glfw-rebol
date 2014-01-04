#! /usr/bin/rebol
REBOL [
	Title:		"Rebol Utilities"
	Author:		"Franois Jouen"
	Rights:		"Copyright (c) 2012-2013 Franois Jouen. All rights reserved."
	License: 	"BSD-3 - https:;github.com/dockimbel/Red/blob/master/BSD-3-License.txt"
]

do %rtypes.r
; a collection of tools made by famous rebolers

;from Piotr Gapinski" %ieee.r
  
from-ieee: func [
 "Zamienia binarna liczbe float ieee-32 na number!"
 [catch]
  dat [binary!] "liczba w formacie ieee-32"
 /local ieee-sign ieee-exponent ieee-mantissa] [

  ieee-sign: func [dat] [either zero? ((to-integer dat) and (to-integer 2#{10000000000000000000000000000000})) [1][-1]] ;; 1 bit
  ieee-exponent: func [dat] [
    exp: (to-integer dat) and (to-integer 2#{01111111100000000000000000000000}) ;; 8 bitow
    exp: (exp / power 2 23) - 127 ;; 127=[2^(k-1) - 1] (k=8 dla IEEE-32bit)
  ]
  ieee-mantissa: func [dat] [
    ((to-integer dat) and 
     (to-integer 2#{00000000011111111111111111111111})) + (to-integer (1 * power 2 23)) ;; 23 bity
  ]

  s: ieee-sign dat
  e: ieee-exponent dat
  m: ieee-mantissa dat
  d: s * (to-integer m) / power 2 (23 - e)
]

to-ieee: func [
 "Zamienia decimal! lub integer! na binary! w formacie ieee-32."
 [catch]
  dat [number!] "liczba do konwersji (24 bity)"
 /local ieee-sign ieee-exponent ieee-mantissa integer-to-binary] [

  integer-to-binary: func [i [number!]] [debase/base to-hex i 16]
  ieee-sign: func [dat] [either positive? dat [0][1]]
  ieee-exponent: func [dat] [ ;; only for -0.5 > x > 0.5
    dat: to-integer dat
    weight: to-integer #{800000}
    i: 0
    forever [
      i: i + 1 
      if ((weight and dat) = weight) [break] 
      weight: to-integer (weight / 2)
    ]
    24 - i + 127
  ]
  ieee-mantissa: func [dat e] [
    m: to-integer (dat * (power 2 (23 - e + 127)))
    m: m and to-integer 2#{0111 1111 1111 1111 1111 1111}
  ]

  s: ieee-sign dat
  dat: abs dat
  e: ieee-exponent dat
  m: ieee-mantissa dat e
  integer-to-binary to-integer (m + (e * power 2 23) + (s * power 2 31))
]

;from "Glenn M. Lewis"  %bin-to-float.r

bin-to-float: func [
    "Converts a binary series to a series of floats"
    dat [binary!] "Binary data to be converted to floats"
    /local result val
] [
    result: copy []
    for i ((length? dat) / 4) 1 -1 [
        val: from-ieee skip dat (4 * i - 4)
        insert result val
    ]
    result
]

float-to-bin: func [
    "Converts a series of floats to a binary series"
    dat [series!] "Float series to be converted to binary"
    /local result val
] [
    result: copy #{}
    for i (length? dat) 1 -1 [
        val: to-ieee pick dat i
        insert result val
    ]
    result
]

; Nenad Rakocevic' routines for memory release
zero-char: #0
malloc: func [size [integer!] "size in bytes"][head insert/dup copy {} zero-char size]
free-mem: func ['word] [set :word make none! recycle]

; this a slight adaptation of fabulous memory access functions written by Ladislav Mecir;
; just introducing local pointers inside func
;see %library-utils.r on rebol.org for original

sizeof: func [
		{get the size of a datatype in bytes}
		datatype [word! block!]
	] [
		length? third make struct! compose/deep [value [(datatype)]] none
]

string-address?: func [
		{get the address of the given string}
		string [any-string!]
		/local str ptr
	] [
	    ptr: make struct! int-ptr! none
	    str: make struct! char* none
		str/buffer: string
		change third ptr third str
		ptr/int
	]

address-to-string: func [
		{get a copy of the nul-terminated string at the given address}
		address [integer!]
		/local str ptr
	] [
		ptr: make struct! int-ptr! reduce [address]
	    str: make struct! char* none
		change third str third ptr
		str/buffer
	]
	
struct-address?: func [
		{get the address of the given struct}
		struct [struct!]
	] [
		string-address? third struct
	]


	
; specific for binary (char-array)
get-memory: func [
		{
			copy a region of memory having the given address and size,
			the result is a REBOL binary value
		}
		address [integer!]
		size [integer!]
		/local ptr struct
	] [
	    ptr: make struct! int-ptr! reduce [address]
		struct: make struct! compose/deep [bin [char-array (size)]] none
		change third struct third ptr
		as-binary struct/bin
]
	
	
set-memory: func [
		{change a region of memory at the given address}
		address [integer!]
		contents [binary! string!]
		/local ptr 
	] [
		ptr: make struct! int-ptr! reduce [address]
		pStruct: make struct! struct* none
		foreach char as-string contents [
			change third pStruct third ptr
			pStruct/struct/c: char
			ptr/int: ptr/int + 1
		]
]


;can be used with strings but slower with /part
get-mem?: func [
    {get the byte from a memory address}
    address [integer!]
    /nts {a null-terminated string}
    /part {a binary with a specified length}
    length [integer!]
] [
    use [m] [
        address: make struct! [i [integer!]] reduce [address]
        if nts [
            m: make struct! [s [string!]] none
            change third m third address
            return m/s
        ]
        if part [
            m: head insert/dup copy [] [. [char!]] length
            m: make struct! compose/deep [bin [struct! (reduce [m])]] none
            change third m third address
            return third m/bin
        ]
        m: make struct! [c [struct! [chr [char!]]]] none
        change third m third address
        m/c/chr
    ]
]
	

set-mem: function [
    {set a byte at a specific memory address}
    address [integer!]
    value [char!]
] [m] [
    address: make struct! [i [integer!]] reduce [address]
    m: make struct! [c [struct! [chr [char!]]]] none
    change third m third address
    m/c/chr: value
]

convert: func [
    x
    /to type [word!]
    /local y
] [
    any [to type: type?/word x]
    y: make struct! compose/deep [x [(type)]] reduce [x]
    third y
]


reverse-conversion: func [
    x [binary!]
    type [word!]
    /local y
] [
    y: make struct! compose/deep [x [(type)]] none
    change third y x
    y/x
]


__convert: func [
		{
			convert block to binary,
			binary to block,
			or memory region to block
		}
		from [block! binary! integer!]
		spec [block!] {
			type specification, supported types are listed in
			http://www.rebol.com/docs/library.html
		}
		/local result struct size ptr
	] [
	    ptr: make struct! int-ptr! none
		switch type? from [
			#[datatype! block!] [
				result: copy #{}
				repeat i min length? from length? spec [
					append result third make struct! compose/deep [
						value [(pick spec i)]
					] reduce [pick from i]			
				]
			]
			#[datatype! binary!] [
				result: copy []
				foreach type spec [
					struct: make struct! compose/deep [value [(type)]] none
					size: length? third struct
					if size > length? from [break]
					change third struct copy/part from size
					append result struct/value
					from: skip from size
				]
			]
			#[datatype! integer!] [
				result: copy []
				foreach type spec [
					struct: make struct! compose/deep [
						s [struct! [[save] value [(type)]]]
					] none
					size: length? third struct/s
					ptr/int: from
					change third struct third ptr
					append result struct/s/value
					from: from + size
				]
			]
		]
		result
	]



