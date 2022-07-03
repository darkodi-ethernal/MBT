--------------------------- MODULE BinSearch0 ---------------------------------
EXTENDS Integers, Sequences, Apalache

CONSTANTS
    \* The input sequence.
    \*
    \* @type: Seq(Int);
    INPUT_SEQ,
    \* The key to search for.
    \*
    \* @type: Int;
    INPUT_KEY,
    \* Bit-width of machine integers.
    \*
    \* @type: Int;
    INT_WIDTH,
    \* the largest value of an unsigned integer
    MAX_UINT == 2^INT_WIDTH
    \* the largest value of a signed integer
    MAX_INT  == 2^(INT_WIDTH - 1) - 1
    \* the smallest value of a signed integer
    MIN_INT  == -2^(INT_WIDTH - 1)

Init == TRUE

Next == TRUE

===============================================================================

