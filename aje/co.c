#include <stdio.h>
#include <assert.h>

#define BLACK 0
#define WHITE 1

#define NONE	0
#define PAWN	1
#define KNIGHT	2
#define BISHOP	3
#define ROOK	4
#define QUEEN	5
#define KING	6

#define NROWS	8
#define NCOLS	8

typedef char Color;
typedef char Piece;
typedef char Board[NCOLS * NROWS];

#define NBITS_PIECE_TYPE	3
#define PIECE_TYPE_MASK		((1 << NBITS_PIECE_TYPE) - 1)

#define PIECE_COLOR(P)		((P) >> NBITS_PIECE_TYPE)
#define PIECE_TYPE(P)		((P) & PIECE_TYPE_MASK)
#define MK_PIECE(COLOR, TYPE)	((COLOR) << NBITS_PIECE_TYPE | (TYPE))

#define BOARD_AT(B, I, J)	(B)[NCOLS * (I) + (J)]
#define VALID_POS(I, J)		(0 <= (I) && (I) < NROWS && 0 <= (J) && (J) < NCOLS)

int pawn_valid_moves(Board board, int i, int j)
{
	assert(PIECE_TYPE(BOARD_AT(board, i, j)) == PAWN);
	if (PIECE_COLOR(
	int direction 
}

int valid_moves(Color player_color, Board board)
{
	int i, j;
	for (i = 0; i < NROWS; i++) {
		for (j = 0; j < NCOLS; j++) {
			Piece p = BOARD_AT(board, i, j);
			if (PIECE_COLOR(p) != player_color) continue;
			switch (PIECE_TYPE(p)) {
			case PAWN:
				pawn_valid_moves(board, i, j);
				break;
			}
		}
	}
}

void initial_board(Board b)
{
	int i, j;
	for (i = 0; i < NROWS; i++) {
		for (j = 0; j < NCOLS; j++) {
			BOARD_AT(b, i, j) = NONE;
		}
	}
	/* Pawns */
	for (j = 0; j < NCOLS; j++) {
		BOARD_AT(b, 1, j) = MK_PIECE(WHITE, PAWN);
		BOARD_AT(b, 6, j) = MK_PIECE(BLACK, PAWN);
	}
	/* Rooks */
	BOARD_AT(b, 0, 0) = MK_PIECE(WHITE, ROOK);
	BOARD_AT(b, 0, 7) = MK_PIECE(WHITE, ROOK);
	BOARD_AT(b, 7, 0) = MK_PIECE(BLACK, ROOK);
	BOARD_AT(b, 7, 7) = MK_PIECE(BLACK, ROOK);
	/* Knights */
	BOARD_AT(b, 0, 1) = MK_PIECE(WHITE, KNIGHT);
	BOARD_AT(b, 0, 6) = MK_PIECE(WHITE, KNIGHT);
	BOARD_AT(b, 7, 1) = MK_PIECE(BLACK, KNIGHT);
	BOARD_AT(b, 7, 6) = MK_PIECE(BLACK, KNIGHT);
	/* Bishops */
	BOARD_AT(b, 0, 2) = MK_PIECE(WHITE, BISHOP);
	BOARD_AT(b, 0, 5) = MK_PIECE(WHITE, BISHOP);
	BOARD_AT(b, 7, 2) = MK_PIECE(BLACK, BISHOP);
	BOARD_AT(b, 7, 5) = MK_PIECE(BLACK, BISHOP);
	/* Queens and kings */
	BOARD_AT(b, 0, 3) = MK_PIECE(WHITE, KING);
	BOARD_AT(b, 0, 4) = MK_PIECE(WHITE, QUEEN);
	BOARD_AT(b, 7, 3) = MK_PIECE(BLACK, KING);
	BOARD_AT(b, 7, 4) = MK_PIECE(BLACK, QUEEN);
}

void print_board(Board b)
{
	int ii, j;
	for (ii = 0; ii < NROWS; ii++) {
		for (j = 0; j < NCOLS; j++) {
			int i = NCOLS - 1 - ii;
			Piece p = BOARD_AT(b, i, j);
			char pt = ' ';
			char pc = ' ';
			switch (PIECE_TYPE(p)) {
			case NONE: pt = ' '; break;
			case PAWN: pt = 'P'; break;
			case KNIGHT: pt = 'N'; break;
			case BISHOP: pt = 'B'; break;
			case ROOK: pt = 'R'; break;
			case QUEEN: pt = 'Q'; break;
			case KING: pt = 'K'; break;
			}
			if (PIECE_TYPE(p) == NONE) {
				pc = ' ';
			} else if (PIECE_COLOR(p) == BLACK) {
				pc = '*';
			} else {
				pc = ' ';
			}
			printf("|%c%c", pt, pc);
		}
		printf("|\n");
	}
}

int main()
{
	Board b;
	initial_board(b);
	print_board(b);
	return 0;
}
