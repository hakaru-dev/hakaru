" Vim syntax file
" Language:     Hakaru
" Maintainer:   Rob Zinkov <rob at zinkov dot com>
" Last Change:  2014-05-18
"

if exists("b:current_syntax")
    finish
endif

"
" Keywords
"

syn keyword hakaruStatement     return
syn keyword hakaruStatement     def fn nextgroup=hakaruFunction skipwhite
syn keyword hakaruConditional   if else
syn keyword hakaruOperator      and not or

syn match   hakaruFunction    "[a-zA-Z_][a-zA-Z0-9_]*" display contained
syn keyword hakaruBoolean     True False
syn match   hakaruFunction    "\%([^[:cntrl:][:space:][:punct:][:digit:]]\|_\)\%([^[:cntrl:][:punct:][:space:]]\|_\)*" display contained

"
" Comments
"

syn match   hakaruComment	"#.*$" display contains=hakaruTodo,@Spell

"
" Strings
"

syn region hakaruBytes		start=+[bB]'+ skip=+\\\\\|\\'\|\\$+ excludenl end=+'+ end=+$+ keepend contains=hakaruBytesError,hakaruBytesContent,@Spell
syn region hakaruBytes		start=+[bB]"+ skip=+\\\\\|\\"\|\\$+ excludenl end=+"+ end=+$+ keepend contains=hakaruBytesError,hakaruBytesContent,@Spell
syn region hakaruBytes		start=+[bB]"""+ end=+"""+ keepend contains=hakaruBytesError,hakaruBytesContent,hakaruDocTest2,hakaruSpaceError,@Spell
syn region hakaruBytes		start=+[bB]'''+ end=+'''+ keepend contains=hakaruBytesError,hakaruBytesContent,hakaruDocTest,hakaruSpaceError,@Spell


syn match hakaruBytesEscape       +\\[abfnrtv'"\\]+ display contained
syn match hakaruBytesEscape       "\\\o\o\=\o\=" display contained
syn match hakaruBytesEscapeError  "\\\o\{,2}[89]" display contained
syn match hakaruBytesEscape       "\\x\x\{2}" display contained
syn match hakaruBytesEscapeError  "\\x\x\=\X" display contained
syn match hakaruBytesEscape       "\\$"

syn match hakaruUniEscape         "\\u\x\{4}" display contained
syn match hakaruUniEscapeError    "\\u\x\{,3}\X" display contained
syn match hakaruUniEscape         "\\U\x\{8}" display contained
syn match hakaruUniEscapeError    "\\U\x\{,7}\X" display contained
syn match hakaruUniEscape         "\\N{[A-Z ]\+}" display contained
syn match hakaruUniEscapeError    "\\N{[^A-Z ]\+}" display contained

syn region hakaruString   start=+'+ skip=+\\\\\|\\'\|\\$+ excludenl end=+'+ end=+$+ keepend contains=hakaruBytesEscape,hakaruBytesEscapeError,hakaruUniEscape,hakaruUniEscapeError,@Spell
syn region hakaruString   start=+"+ skip=+\\\\\|\\"\|\\$+ excludenl end=+"+ end=+$+ keepend contains=hakaruBytesEscape,hakaruBytesEscapeError,hakaruUniEscape,hakaruUniEscapeError,@Spell
syn region hakaruString   start=+"""+ end=+"""+ keepend contains=hakaruBytesEscape,hakaruBytesEscapeError,hakaruUniEscape,hakaruUniEscapeError,hakaruDocTest2,hakaruSpaceError,@Spell
syn region hakaruString   start=+'''+ end=+'''+ keepend contains=hakaruBytesEscape,hakaruBytesEscapeError,hakaruUniEscape,hakaruUniEscapeError,hakaruDocTest,hakaruSpaceError,@Spell

syn match hakaruRawEscape +\\['"]+ display transparent contained

"
" Numbers (ints, longs, floats, complex)
"

syn match   hakaruHexError	"\<0[xX]\x*[g-zG-Z]\+\x*[lL]\=\>" display
syn match   hakaruOctError	"\<0[oO]\=\o*\D\+\d*[lL]\=\>" display
syn match   hakaruBinError	"\<0[bB][01]*\D\+\d*[lL]\=\>" display

syn match   hakaruHexNumber	"\<0[xX]\x\+[lL]\=\>" display
syn match   hakaruOctNumber "\<0[oO]\o\+[lL]\=\>" display
syn match   hakaruBinNumber "\<0[bB][01]\+[lL]\=\>" display

syn match   hakaruNumberError	"\<\d\+\D[lL]\=\>" display
syn match   hakaruNumber	"\<\d[lL]\=\>" display
syn match   hakaruNumber	"\<[0-9]\d\+[lL]\=\>" display
syn match   hakaruNumber	"\<\d\+[lLjJ]\>" display

syn match   hakaruOctError	"\<0[oO]\=\o*[8-9]\d*[lL]\=\>" display
syn match   hakaruBinError	"\<0[bB][01]*[2-9]\d*[lL]\=\>" display

syn match   hakaruFloat		"\.\d\+\%([eE][+-]\=\d\+\)\=[jJ]\=\>" display
syn match   hakaruFloat		"\<\d\+[eE][+-]\=\d\+[jJ]\=\>" display
syn match   hakaruFloat		"\<\d\+\.\d*\%([eE][+-]\=\d\+\)\=[jJ]\=" display

"
" Builtin objects and types
"

syn keyword hakaruBoolean		True False

"
" Builtin functions
"

syn keyword hakaruBuiltinFunc	pow sin cos
syn keyword hakaruBuiltinFunc	normal bern uniform dirac gamma beta
syn keyword hakaruBuiltinFunc	nat int prob real

hi def link hakaruStatement        Statement
hi def link hakaruImport           Include
hi def link hakaruFunction         Function
hi def link hakaruConditional      Conditional
hi def link hakaruRepeat           Repeat
hi def link hakaruException        Exception
hi def link hakaruOperator         Operator

hi def link hakaruDecorator        Define
hi def link hakaruDottedName       Function
hi def link hakaruDot              Normal

hi def link hakaruComment          Comment

hi def link hakaruString           String
hi def link hakaruRawString        String

hi def link hakaruUniEscape        Special
hi def link hakaruUniEscapeError   Error

hi def link hakaruNumber           Number
hi def link hakaruHexNumber        Number
hi def link hakaruOctNumber        Number
hi def link hakaruBinNumber        Number
hi def link hakaruFloat            Float
hi def link hakaruNumberError      Error
hi def link hakaruOctError         Error
hi def link hakaruHexError         Error
hi def link hakaruBinError         Error

hi def link hakaruBoolean          Boolean

hi def link hakaruBuiltinObj       Structure
hi def link hakaruBuiltinFunc      Function

hi def link hakaruExClass          Structure

let b:current_syntax = "hakaru"
