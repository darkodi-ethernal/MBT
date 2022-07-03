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
    INT_WIDTH

Init == TRUE

Next == TRUE

===============================================================================

