// Chess.cs
// -----------------------------------------------------------------------------
// Single-file SIMPL# library, matching the SudokuGames project's structure:
// one project (ChessGames), one source file (Chess.cs), one class (ChessGame)
// that SIMPL+ declares directly by name - "ChessGame game;" - with no
// "object x; x = CREATE OBJECT OF TYPE ...", no main(), no EVENTHANDLER /
// RegisterDelegate. Chess.usp calls an action method (NewGame/MakeMove/
// Resign/MakeCpuMove) and then polls the Get*() methods below to refresh the
// panel, the same call-then-RefreshUI() pattern Sudoku.usp uses.
//
// Everything - board representation, legal move generation, check/checkmate/
// stalemate/draw detection, castling, en passant, promotion, a simple
// material-based CPU opponent, resignation handling, and the SIMPL+ facing
// wrapper - lives in this one file on purpose.
// -----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Text;
using Crestron.SimplSharp; // SimplSharpString
namespace ChessGames
{
    internal enum PieceType : byte { None = 0, Pawn, Knight, Bishop, Rook, Queen, King }
    internal enum PieceColor : byte { None = 0, White, Black }
    internal struct Piece
    {
        public PieceType Type;
        public PieceColor Color;
        public static readonly Piece Empty = new Piece { Type = PieceType.None, Color = PieceColor.None };
        public bool IsEmpty { get { return Type == PieceType.None; } }
        public char ToChar()
        {
            char c;
            switch (Type)
            {
                case PieceType.Pawn: c = 'p'; break;
                case PieceType.Knight: c = 'n'; break;
                case PieceType.Bishop: c = 'b'; break;
                case PieceType.Rook: c = 'r'; break;
                case PieceType.Queen: c = 'q'; break;
                case PieceType.King: c = 'k'; break;
                default: return '.';
            }
            return Color == PieceColor.White ? char.ToUpperInvariant(c) : c;
        }
        public static PieceType TypeFromChar(char c)
        {
            switch (char.ToLowerInvariant(c))
            {
                case 'p': return PieceType.Pawn;
                case 'n': return PieceType.Knight;
                case 'b': return PieceType.Bishop;
                case 'r': return PieceType.Rook;
                case 'q': return PieceType.Queen;
                case 'k': return PieceType.King;
                default: return PieceType.None;
            }
        }
    }
    internal struct Square
    {
        public int File; // 0=a ... 7=h
        public int Rank; // 0=rank1 ... 7=rank8
        public Square(int file, int rank) { File = file; Rank = rank; }
        public bool IsValid { get { return File >= 0 && File <= 7 && Rank >= 0 && Rank <= 7; } }
        public static bool TryParse(string algebraic, out Square square)
        {
            square = new Square(-1, -1);
            if (string.IsNullOrEmpty(algebraic) || algebraic.Length != 2) return false;
            char fileChar = char.ToLowerInvariant(algebraic[0]);
            char rankChar = algebraic[1];
            if (fileChar < 'a' || fileChar > 'h') return false;
            if (rankChar < '1' || rankChar > '8') return false;
            square = new Square(fileChar - 'a', rankChar - '1');
            return true;
        }
        public override string ToString()
        {
            return string.Format("{0}{1}", (char)('a' + File), Rank + 1);
        }
    }
    internal class Move
    {
        public Square From;
        public Square To;
        public PieceType Promotion; // PieceType.None if not a promotion
        public bool IsCastleKingSide;
        public bool IsCastleQueenSide;
        public bool IsEnPassantCapture;
        public Piece CapturedPiece;
        public override string ToString()
        {
            string promo = Promotion == PieceType.None ? "" : char.ToLowerInvariant(new Piece { Type = Promotion, Color = PieceColor.Black }.ToChar()).ToString();
            return From.ToString() + To.ToString() + promo;
        }
    }
    internal enum MoveResultCode
    {
        Illegal = 0,
        Ok,
        OkCheck,
        OkCheckmate,
        OkStalemate,
        OkDrawFiftyMove,
        OkDrawInsufficientMaterial,
        NotYourTurn,
        NoPieceOnSquare,
        GameAlreadyOver,
        Resignation
    }
    internal class MoveResult
    {
        public MoveResultCode Code;
        public Move Move;
        public bool Success { get { return Code != MoveResultCode.Illegal && Code != MoveResultCode.NotYourTurn && Code != MoveResultCode.NoPieceOnSquare && Code != MoveResultCode.GameAlreadyOver; } }
    }
    // -------------------------------------------------------------------
    // Core rules engine
    // -------------------------------------------------------------------
    internal class ChessEngine
    {
        private Piece[,] _board; // [file, rank]
        private PieceColor _sideToMove;
        private bool _whiteCanCastleKingSide, _whiteCanCastleQueenSide;
        private bool _blackCanCastleKingSide, _blackCanCastleQueenSide;
        private Square _enPassantTarget; // invalid square if none
        private int _halfmoveClock;
        private int _fullmoveNumber;
        private bool _gameOver;
        private PieceColor _resignedColor = PieceColor.None;
        private readonly List<string> _capturedByWhite = new List<string>(); // pieces White has captured (black pieces)
        private readonly List<string> _capturedByBlack = new List<string>();
        private readonly List<string> _positionHistory = new List<string>(); // simplified position keys, for threefold repetition
        private readonly Random _rng = new Random();
        public Move LastMove { get; private set; }
        /// <summary>
        /// The MoveResultCode from the most recent successful TryMove() (or
        /// Ok after NewGame()). Lets a poll-based caller ask "was the last
        /// move checkmate/stalemate/a draw?" after the fact.
        /// </summary>
        public MoveResultCode LastResultCode { get; private set; }
        public ChessEngine()
        {
            NewGame();
        }
        public void NewGame()
        {
            _board = new Piece[8, 8];
            SetupBackRank(0, PieceColor.White);
            SetupBackRank(7, PieceColor.Black);
            for (int f = 0; f < 8; f++)
            {
                _board[f, 1] = new Piece { Type = PieceType.Pawn, Color = PieceColor.White };
                _board[f, 6] = new Piece { Type = PieceType.Pawn, Color = PieceColor.Black };
            }
            _sideToMove = PieceColor.White;
            _whiteCanCastleKingSide = _whiteCanCastleQueenSide = true;
            _blackCanCastleKingSide = _blackCanCastleQueenSide = true;
            _enPassantTarget = new Square(-1, -1);
            _halfmoveClock = 0;
            _fullmoveNumber = 1;
            _gameOver = false;
            _resignedColor = PieceColor.None;
            _capturedByWhite.Clear();
            _capturedByBlack.Clear();
            _positionHistory.Clear();
            LastMove = null;
            LastResultCode = MoveResultCode.Ok;
            _positionHistory.Add(PositionKey());
        }
        private void SetupBackRank(int rank, PieceColor color)
        {
            PieceType[] order = { PieceType.Rook, PieceType.Knight, PieceType.Bishop, PieceType.Queen, PieceType.King, PieceType.Bishop, PieceType.Knight, PieceType.Rook };
            for (int f = 0; f < 8; f++)
                _board[f, rank] = new Piece { Type = order[f], Color = color };
        }
        public PieceColor SideToMove { get { return _sideToMove; } }
        public bool IsGameOver { get { return _gameOver; } }
        public int FullmoveNumber { get { return _fullmoveNumber; } }
        public int HalfmoveClock { get { return _halfmoveClock; } }
        public MoveResult TryMove(string fromAlgebraic, string toAlgebraic, char promotionChar)
        {
            var result = new MoveResult();
            if (_gameOver) { result.Code = MoveResultCode.GameAlreadyOver; return result; }
            Square from, to;
            if (!Square.TryParse(fromAlgebraic, out from) || !Square.TryParse(toAlgebraic, out to))
            {
                result.Code = MoveResultCode.Illegal;
                return result;
            }
            Piece moving = _board[from.File, from.Rank];
            if (moving.IsEmpty)
            {
                result.Code = MoveResultCode.NoPieceOnSquare;
                return result;
            }
            if (moving.Color != _sideToMove)
            {
                result.Code = MoveResultCode.NotYourTurn;
                return result;
            }
            PieceType promotion = PieceType.None;
            if (promotionChar != '\0')
                promotion = Piece.TypeFromChar(promotionChar);
            List<Move> legalMoves = GenerateLegalMoves(_sideToMove);
            Move chosen = null;
            foreach (var m in legalMoves)
            {
                if (m.From.File == from.File && m.From.Rank == from.Rank &&
                    m.To.File == to.File && m.To.Rank == to.Rank)
                {
                    if (m.Promotion != PieceType.None)
                    {
                        PieceType wanted = promotion == PieceType.None ? PieceType.Queen : promotion;
                        if (m.Promotion == wanted) { chosen = m; break; }
                    }
                    else
                    {
                        chosen = m;
                        break;
                    }
                }
            }
            if (chosen == null)
            {
                result.Code = MoveResultCode.Illegal;
                return result;
            }
            ApplyMove(chosen);
            result.Move = chosen;
            result.Code = EvaluateGameStateAfterMove();
            LastResultCode = result.Code;
            return result;
        }
        /// <summary>
        /// Picks and plays a move for whichever color is currently to move,
        /// using a simple material-based heuristic: prefer captures, avoid
        /// leaving the moved piece immediately recapturable, mildly prefer
        /// giving check. Ties are broken randomly. Intended to be called
        /// from SIMPL+ right after a human move completes, when the CPU is
        /// controlling the side now on move.
        /// </summary>
        public MoveResult MakeCpuMove()
        {
            var result = new MoveResult();
            if (_gameOver) { result.Code = MoveResultCode.GameAlreadyOver; return result; }
            PieceColor color = _sideToMove;
            List<Move> legalMoves = GenerateLegalMoves(color);
            if (legalMoves.Count == 0)
            {
                result.Code = MoveResultCode.Illegal;
                return result;
            }
            Move chosen = ChooseCpuMove(legalMoves, color);
            ApplyMove(chosen);
            result.Move = chosen;
            result.Code = EvaluateGameStateAfterMove();
            LastResultCode = result.Code;
            return result;
        }
        private Move ChooseCpuMove(List<Move> legalMoves, PieceColor color)
        {
            double bestScore = double.NegativeInfinity;
            var bestMoves = new List<Move>();
            foreach (var m in legalMoves)
            {
                double score = ScoreCpuMove(m, color);
                if (score > bestScore + 0.0001)
                {
                    bestScore = score;
                    bestMoves.Clear();
                    bestMoves.Add(m);
                }
                else if (score > bestScore - 0.0001 && score < bestScore + 0.0001)
                {
                    bestMoves.Add(m);
                }
            }
            if (bestMoves.Count == 0) return legalMoves[0];
            return bestMoves[_rng.Next(bestMoves.Count)];
        }
        /// <summary>
        /// Material-based score for one candidate move: value of anything it
        /// captures, minus the value of the moved piece if the destination
        /// square would then be attacked by the opponent, plus a small bonus
        /// for delivering check. Simulates the move on the real board and
        /// restores it afterward (same clone/restore approach as
        /// MoveLeavesKingInCheck).
        /// </summary>
        private double ScoreCpuMove(Move m, PieceColor color)
        {
            double score = 0;
            Piece capturedPiece = _board[m.To.File, m.To.Rank];
            if (m.IsEnPassantCapture)
            {
                int epRank = color == PieceColor.White ? m.To.Rank - 1 : m.To.Rank + 1;
                capturedPiece = _board[m.To.File, epRank];
            }
            if (!capturedPiece.IsEmpty)
                score += PieceValue(capturedPiece.Type);
            Piece[,] savedBoard = (Piece[,])_board.Clone();
            Square savedEnPassant = _enPassantTarget;
            Piece moving = _board[m.From.File, m.From.Rank];
            if (m.IsEnPassantCapture)
            {
                int epRank = color == PieceColor.White ? m.To.Rank - 1 : m.To.Rank + 1;
                _board[m.To.File, epRank] = Piece.Empty;
            }
            _board[m.From.File, m.From.Rank] = Piece.Empty;
            Piece placed = moving;
            if (m.Promotion != PieceType.None) placed = new Piece { Type = m.Promotion, Color = moving.Color };
            _board[m.To.File, m.To.Rank] = placed;
            if (m.IsCastleKingSide)
            {
                int rank = color == PieceColor.White ? 0 : 7;
                _board[5, rank] = _board[7, rank];
                _board[7, rank] = Piece.Empty;
            }
            else if (m.IsCastleQueenSide)
            {
                int rank = color == PieceColor.White ? 0 : 7;
                _board[3, rank] = _board[0, rank];
                _board[0, rank] = Piece.Empty;
            }
            PieceColor opponent = Opponent(color);
            if (IsSquareAttacked(m.To, opponent))
            {
                score -= PieceValue(placed.Type);
            }
            if (IsKingInCheck(opponent))
            {
                score += 0.5;
            }
            _board = savedBoard;
            _enPassantTarget = savedEnPassant;
            return score;
        }
        private static int PieceValue(PieceType t)
        {
            switch (t)
            {
                case PieceType.Pawn: return 1;
                case PieceType.Knight: return 3;
                case PieceType.Bishop: return 3;
                case PieceType.Rook: return 5;
                case PieceType.Queen: return 9;
                default: return 0;
            }
        }
        private MoveResultCode EvaluateGameStateAfterMove()
        {
            PieceColor opponent = _sideToMove; // side to move already flipped in ApplyMove
            bool inCheck = IsKingInCheck(opponent);
            List<Move> opponentMoves = GenerateLegalMoves(opponent);
            if (opponentMoves.Count == 0)
            {
                _gameOver = true;
                return inCheck ? MoveResultCode.OkCheckmate : MoveResultCode.OkStalemate;
            }
            if (_halfmoveClock >= 100) // 50 full moves = 100 half-moves
            {
                _gameOver = true;
                return MoveResultCode.OkDrawFiftyMove;
            }
            if (IsInsufficientMaterial())
            {
                _gameOver = true;
                return MoveResultCode.OkDrawInsufficientMaterial;
            }
            int repeats = 0;
            string key = PositionKey();
            foreach (var k in _positionHistory) if (k == key) repeats++;
            if (repeats >= 3)
            {
                _gameOver = true;
                return MoveResultCode.OkDrawFiftyMove; // reuse code for "draw"
            }
            return inCheck ? MoveResultCode.OkCheck : MoveResultCode.Ok;
        }
        public bool IsInCheck(PieceColor color)
        {
            return IsKingInCheck(color);
        }
        public void Resign(PieceColor resigningColor)
        {
            _gameOver = true;
            _resignedColor = resigningColor;
            LastResultCode = MoveResultCode.Resignation;
        }
        private void ApplyMove(Move m)
        {
            Piece moving = _board[m.From.File, m.From.Rank];
            Piece captured = _board[m.To.File, m.To.Rank];
            bool isPawnMove = moving.Type == PieceType.Pawn;
            bool isCapture = !captured.IsEmpty || m.IsEnPassantCapture;
            if (m.IsEnPassantCapture)
            {
                int capturedRank = moving.Color == PieceColor.White ? m.To.Rank - 1 : m.To.Rank + 1;
                captured = _board[m.To.File, capturedRank];
                _board[m.To.File, capturedRank] = Piece.Empty;
            }
            if (isCapture)
            {
                m.CapturedPiece = captured;
                string letter = new Piece { Type = captured.Type, Color = captured.Color }.ToChar().ToString();
                if (moving.Color == PieceColor.White) _capturedByWhite.Add(letter);
                else _capturedByBlack.Add(letter);
            }
            _board[m.From.File, m.From.Rank] = Piece.Empty;
            Piece placed = moving;
            if (m.Promotion != PieceType.None)
                placed = new Piece { Type = m.Promotion, Color = moving.Color };
            _board[m.To.File, m.To.Rank] = placed;
            if (m.IsCastleKingSide)
            {
                int rank = moving.Color == PieceColor.White ? 0 : 7;
                _board[5, rank] = _board[7, rank];
                _board[7, rank] = Piece.Empty;
            }
            else if (m.IsCastleQueenSide)
            {
                int rank = moving.Color == PieceColor.White ? 0 : 7;
                _board[3, rank] = _board[0, rank];
                _board[0, rank] = Piece.Empty;
            }
            if (moving.Type == PieceType.King)
            {
                if (moving.Color == PieceColor.White) { _whiteCanCastleKingSide = false; _whiteCanCastleQueenSide = false; }
                else { _blackCanCastleKingSide = false; _blackCanCastleQueenSide = false; }
            }
            if (moving.Type == PieceType.Rook)
            {
                if (m.From.File == 0 && m.From.Rank == 0) _whiteCanCastleQueenSide = false;
                if (m.From.File == 7 && m.From.Rank == 0) _whiteCanCastleKingSide = false;
                if (m.From.File == 0 && m.From.Rank == 7) _blackCanCastleQueenSide = false;
                if (m.From.File == 7 && m.From.Rank == 7) _blackCanCastleKingSide = false;
            }
            if (m.To.File == 0 && m.To.Rank == 0) _whiteCanCastleQueenSide = false;
            if (m.To.File == 7 && m.To.Rank == 0) _whiteCanCastleKingSide = false;
            if (m.To.File == 0 && m.To.Rank == 7) _blackCanCastleQueenSide = false;
            if (m.To.File == 7 && m.To.Rank == 7) _blackCanCastleKingSide = false;
            _enPassantTarget = new Square(-1, -1);
            if (isPawnMove && Math.Abs(m.To.Rank - m.From.Rank) == 2)
            {
                _enPassantTarget = new Square(m.From.File, (m.From.Rank + m.To.Rank) / 2);
            }
            if (isPawnMove || isCapture) _halfmoveClock = 0;
            else _halfmoveClock++;
            if (moving.Color == PieceColor.Black) _fullmoveNumber++;
            _sideToMove = moving.Color == PieceColor.White ? PieceColor.Black : PieceColor.White;
            LastMove = m;
            _positionHistory.Add(PositionKey());
        }
        public List<Move> GenerateLegalMoves(PieceColor color)
        {
            var pseudo = GeneratePseudoLegalMoves(color);
            var legal = new List<Move>();
            foreach (var m in pseudo)
            {
                if (!MoveLeavesKingInCheck(m, color))
                    legal.Add(m);
            }
            return legal;
        }
        private bool MoveLeavesKingInCheck(Move m, PieceColor color)
        {
            Piece[,] savedBoard = (Piece[,])_board.Clone();
            Square savedEnPassant = _enPassantTarget;
            Piece moving = _board[m.From.File, m.From.Rank];
            if (m.IsEnPassantCapture)
            {
                int capturedRank = moving.Color == PieceColor.White ? m.To.Rank - 1 : m.To.Rank + 1;
                _board[m.To.File, capturedRank] = Piece.Empty;
            }
            _board[m.From.File, m.From.Rank] = Piece.Empty;
            Piece placed = moving;
            if (m.Promotion != PieceType.None) placed = new Piece { Type = m.Promotion, Color = moving.Color };
            _board[m.To.File, m.To.Rank] = placed;
            if (m.IsCastleKingSide)
            {
                int rank = moving.Color == PieceColor.White ? 0 : 7;
                _board[5, rank] = _board[7, rank];
                _board[7, rank] = Piece.Empty;
            }
            else if (m.IsCastleQueenSide)
            {
                int rank = moving.Color == PieceColor.White ? 0 : 7;
                _board[3, rank] = _board[0, rank];
                _board[0, rank] = Piece.Empty;
            }
            bool inCheck = IsKingInCheck(color);
            _board = savedBoard;
            _enPassantTarget = savedEnPassant;
            return inCheck;
        }
        private List<Move> GeneratePseudoLegalMoves(PieceColor color)
        {
            var moves = new List<Move>();
            for (int f = 0; f < 8; f++)
            {
                for (int r = 0; r < 8; r++)
                {
                    Piece p = _board[f, r];
                    if (p.IsEmpty || p.Color != color) continue;
                    Square from = new Square(f, r);
                    switch (p.Type)
                    {
                        case PieceType.Pawn: AddPawnMoves(moves, from, color); break;
                        case PieceType.Knight: AddKnightMoves(moves, from, color); break;
                        case PieceType.Bishop: AddSlidingMoves(moves, from, color, BishopDirs); break;
                        case PieceType.Rook: AddSlidingMoves(moves, from, color, RookDirs); break;
                        case PieceType.Queen: AddSlidingMoves(moves, from, color, QueenDirs); break;
                        case PieceType.King: AddKingMoves(moves, from, color); break;
                    }
                }
            }
            return moves;
        }
        private static readonly int[,] KnightOffsets = {
            { 1, 2 }, { 2, 1 }, { 2, -1 }, { 1, -2 },
            { -1, -2 }, { -2, -1 }, { -2, 1 }, { -1, 2 }
        };
        private static readonly int[,] BishopDirs = { { 1, 1 }, { 1, -1 }, { -1, 1 }, { -1, -1 } };
        private static readonly int[,] RookDirs = { { 1, 0 }, { -1, 0 }, { 0, 1 }, { 0, -1 } };
        private static readonly int[,] QueenDirs = { { 1, 1 }, { 1, -1 }, { -1, 1 }, { -1, -1 }, { 1, 0 }, { -1, 0 }, { 0, 1 }, { 0, -1 } };
        private static readonly int[,] KingOffsets = { { 1, 1 }, { 1, -1 }, { -1, 1 }, { -1, -1 }, { 1, 0 }, { -1, 0 }, { 0, 1 }, { 0, -1 } };
        private void AddPawnMoves(List<Move> moves, Square from, PieceColor color)
        {
            int dir = color == PieceColor.White ? 1 : -1;
            int startRank = color == PieceColor.White ? 1 : 6;
            int promoRank = color == PieceColor.White ? 7 : 0;
            Square oneAhead = new Square(from.File, from.Rank + dir);
            if (oneAhead.IsValid && _board[oneAhead.File, oneAhead.Rank].IsEmpty)
            {
                AddPawnMoveOrPromotion(moves, from, oneAhead, promoRank);
                if (from.Rank == startRank)
                {
                    Square twoAhead = new Square(from.File, from.Rank + 2 * dir);
                    if (_board[twoAhead.File, twoAhead.Rank].IsEmpty)
                        moves.Add(new Move { From = from, To = twoAhead });
                }
            }
            for (int df = -1; df <= 1; df += 2)
            {
                Square capSq = new Square(from.File + df, from.Rank + dir);
                if (!capSq.IsValid) continue;
                Piece target = _board[capSq.File, capSq.Rank];
                if (!target.IsEmpty && target.Color != color)
                {
                    AddPawnMoveOrPromotion(moves, from, capSq, promoRank);
                }
                else if (_enPassantTarget.IsValid && capSq.File == _enPassantTarget.File && capSq.Rank == _enPassantTarget.Rank)
                {
                    moves.Add(new Move { From = from, To = capSq, IsEnPassantCapture = true });
                }
            }
        }
        private void AddPawnMoveOrPromotion(List<Move> moves, Square from, Square to, int promoRank)
        {
            if (to.Rank == promoRank)
            {
                moves.Add(new Move { From = from, To = to, Promotion = PieceType.Queen });
                moves.Add(new Move { From = from, To = to, Promotion = PieceType.Rook });
                moves.Add(new Move { From = from, To = to, Promotion = PieceType.Bishop });
                moves.Add(new Move { From = from, To = to, Promotion = PieceType.Knight });
            }
            else
            {
                moves.Add(new Move { From = from, To = to });
            }
        }
        private void AddKnightMoves(List<Move> moves, Square from, PieceColor color)
        {
            for (int i = 0; i < 8; i++)
            {
                Square to = new Square(from.File + KnightOffsets[i, 0], from.Rank + KnightOffsets[i, 1]);
                if (!to.IsValid) continue;
                Piece target = _board[to.File, to.Rank];
                if (target.IsEmpty || target.Color != color)
                    moves.Add(new Move { From = from, To = to });
            }
        }
        private void AddSlidingMoves(List<Move> moves, Square from, PieceColor color, int[,] dirs)
        {
            int n = dirs.GetLength(0);
            for (int i = 0; i < n; i++)
            {
                int df = dirs[i, 0], dr = dirs[i, 1];
                Square to = new Square(from.File + df, from.Rank + dr);
                while (to.IsValid)
                {
                    Piece target = _board[to.File, to.Rank];
                    if (target.IsEmpty)
                    {
                        moves.Add(new Move { From = from, To = to });
                    }
                    else
                    {
                        if (target.Color != color) moves.Add(new Move { From = from, To = to });
                        break;
                    }
                    to = new Square(to.File + df, to.Rank + dr);
                }
            }
        }
        private void AddKingMoves(List<Move> moves, Square from, PieceColor color)
        {
            for (int i = 0; i < 8; i++)
            {
                Square to = new Square(from.File + KingOffsets[i, 0], from.Rank + KingOffsets[i, 1]);
                if (!to.IsValid) continue;
                Piece target = _board[to.File, to.Rank];
                if (target.IsEmpty || target.Color != color)
                    moves.Add(new Move { From = from, To = to });
            }
            int rank = color == PieceColor.White ? 0 : 7;
            if (from.File == 4 && from.Rank == rank && !IsKingInCheck(color))
            {
                bool canKingSide = color == PieceColor.White ? _whiteCanCastleKingSide : _blackCanCastleKingSide;
                bool canQueenSide = color == PieceColor.White ? _whiteCanCastleQueenSide : _blackCanCastleQueenSide;
                if (canKingSide &&
                    _board[5, rank].IsEmpty && _board[6, rank].IsEmpty &&
                    !IsSquareAttacked(new Square(5, rank), Opponent(color)) &&
                    !IsSquareAttacked(new Square(6, rank), Opponent(color)))
                {
                    moves.Add(new Move { From = from, To = new Square(6, rank), IsCastleKingSide = true });
                }
                if (canQueenSide &&
                    _board[3, rank].IsEmpty && _board[2, rank].IsEmpty && _board[1, rank].IsEmpty &&
                    !IsSquareAttacked(new Square(3, rank), Opponent(color)) &&
                    !IsSquareAttacked(new Square(2, rank), Opponent(color)))
                {
                    moves.Add(new Move { From = from, To = new Square(2, rank), IsCastleQueenSide = true });
                }
            }
        }
        private static PieceColor Opponent(PieceColor color)
        {
            return color == PieceColor.White ? PieceColor.Black : PieceColor.White;
        }
        private bool IsKingInCheck(PieceColor color)
        {
            Square kingSq = FindKing(color);
            if (!kingSq.IsValid) return false;
            return IsSquareAttacked(kingSq, Opponent(color));
        }
        private Square FindKing(PieceColor color)
        {
            for (int f = 0; f < 8; f++)
                for (int r = 0; r < 8; r++)
                {
                    Piece p = _board[f, r];
                    if (p.Type == PieceType.King && p.Color == color)
                        return new Square(f, r);
                }
            return new Square(-1, -1);
        }
        private bool IsSquareAttacked(Square sq, PieceColor byColor)
        {
            int dir = byColor == PieceColor.White ? 1 : -1;
            for (int df = -1; df <= 1; df += 2)
            {
                Square s = new Square(sq.File + df, sq.Rank - dir);
                if (s.IsValid)
                {
                    Piece p = _board[s.File, s.Rank];
                    if (p.Type == PieceType.Pawn && p.Color == byColor) return true;
                }
            }
            for (int i = 0; i < 8; i++)
            {
                Square s = new Square(sq.File + KnightOffsets[i, 0], sq.Rank + KnightOffsets[i, 1]);
                if (s.IsValid)
                {
                    Piece p = _board[s.File, s.Rank];
                    if (p.Type == PieceType.Knight && p.Color == byColor) return true;
                }
            }
            for (int i = 0; i < 8; i++)
            {
                Square s = new Square(sq.File + KingOffsets[i, 0], sq.Rank + KingOffsets[i, 1]);
                if (s.IsValid)
                {
                    Piece p = _board[s.File, s.Rank];
                    if (p.Type == PieceType.King && p.Color == byColor) return true;
                }
            }
            if (IsAttackedBySliding(sq, byColor, BishopDirs, PieceType.Bishop, PieceType.Queen)) return true;
            if (IsAttackedBySliding(sq, byColor, RookDirs, PieceType.Rook, PieceType.Queen)) return true;
            return false;
        }
        private bool IsAttackedBySliding(Square sq, PieceColor byColor, int[,] dirs, PieceType type1, PieceType type2)
        {
            int n = dirs.GetLength(0);
            for (int i = 0; i < n; i++)
            {
                int df = dirs[i, 0], dr = dirs[i, 1];
                Square s = new Square(sq.File + df, sq.Rank + dr);
                while (s.IsValid)
                {
                    Piece p = _board[s.File, s.Rank];
                    if (!p.IsEmpty)
                    {
                        if (p.Color == byColor && (p.Type == type1 || p.Type == type2)) return true;
                        break;
                    }
                    s = new Square(s.File + df, s.Rank + dr);
                }
            }
            return false;
        }
        private bool IsInsufficientMaterial()
        {
            var minors = new List<Piece>();
            var minorSquares = new List<Square>();
            for (int f = 0; f < 8; f++)
            {
                for (int r = 0; r < 8; r++)
                {
                    Piece p = _board[f, r];
                    if (p.IsEmpty || p.Type == PieceType.King) continue;
                    if (p.Type == PieceType.Pawn || p.Type == PieceType.Rook || p.Type == PieceType.Queen)
                        return false;
                    minors.Add(p);
                    minorSquares.Add(new Square(f, r));
                }
            }
            if (minors.Count == 0) return true;
            if (minors.Count == 1) return true;
            if (minors.Count == 2)
            {
                bool bothKnights = minors[0].Type == PieceType.Knight && minors[1].Type == PieceType.Knight;
                if (bothKnights) return true;
                bool bothBishops = minors[0].Type == PieceType.Bishop && minors[1].Type == PieceType.Bishop;
                if (bothBishops)
                {
                    int color0 = (minorSquares[0].File + minorSquares[0].Rank) % 2;
                    int color1 = (minorSquares[1].File + minorSquares[1].Rank) % 2;
                    return color0 == color1;
                }
                return false;
            }
            return false;
        }
        /// <summary>
        /// Compact 64-character board string, ordered a8,b8,...,h8, a7,...,h1
        /// (standard reading order, top rank first). '.' = empty square.
        /// Uppercase = White, lowercase = Black.
        /// </summary>
        public string GetBoardString()
        {
            var sb = new StringBuilder(64);
            for (int r = 7; r >= 0; r--)
                for (int f = 0; f < 8; f++)
                    sb.Append(_board[f, r].ToChar());
            return sb.ToString();
        }
        public string GetFEN()
        {
            var sb = new StringBuilder();
            for (int r = 7; r >= 0; r--)
            {
                int empty = 0;
                for (int f = 0; f < 8; f++)
                {
                    Piece p = _board[f, r];
                    if (p.IsEmpty) { empty++; continue; }
                    if (empty > 0) { sb.Append(empty); empty = 0; }
                    sb.Append(p.ToChar());
                }
                if (empty > 0) sb.Append(empty);
                if (r > 0) sb.Append('/');
            }
            sb.Append(_sideToMove == PieceColor.White ? " w " : " b ");
            string castle = "";
            if (_whiteCanCastleKingSide) castle += "K";
            if (_whiteCanCastleQueenSide) castle += "Q";
            if (_blackCanCastleKingSide) castle += "k";
            if (_blackCanCastleQueenSide) castle += "q";
            sb.Append(castle.Length == 0 ? "-" : castle);
            sb.Append(' ');
            sb.Append(_enPassantTarget.IsValid ? _enPassantTarget.ToString() : "-");
            sb.Append(' ').Append(_halfmoveClock);
            sb.Append(' ').Append(_fullmoveNumber);
            return sb.ToString();
        }
        private string PositionKey()
        {
            return GetBoardString() + (_sideToMove == PieceColor.White ? "w" : "b") +
                   (_whiteCanCastleKingSide ? "K" : "") + (_whiteCanCastleQueenSide ? "Q" : "") +
                   (_blackCanCastleKingSide ? "k" : "") + (_blackCanCastleQueenSide ? "q" : "") +
                   (_enPassantTarget.IsValid ? _enPassantTarget.ToString() : "-");
        }
        /// <summary>
        /// 64-char mask ('1' = legal destination, '0' = not) in the same
        /// a8..h1 reading order as GetBoardString(), for every square the
        /// piece on fromAlgebraic can legally move to right now.
        /// </summary>
        public string GetLegalDestinationMask(string fromAlgebraic)
        {
            var mask = new char[64];
            for (int i = 0; i < 64; i++) mask[i] = '0';
            Square from;
            if (_gameOver || !Square.TryParse(fromAlgebraic, out from)) return new string(mask);
            Piece piece = _board[from.File, from.Rank];
            if (piece.IsEmpty || piece.Color != _sideToMove) return new string(mask);
            List<Move> legal = GenerateLegalMoves(_sideToMove);
            foreach (var m in legal)
            {
                if (m.From.File == from.File && m.From.Rank == from.Rank)
                {
                    int row = 7 - m.To.Rank;
                    int idx = row * 8 + m.To.File;
                    mask[idx] = '1';
                }
            }
            return new string(mask);
        }
        public string GetCapturedByWhite()
        {
            return string.Join("", _capturedByWhite.ToArray());
        }
        public string GetCapturedByBlack()
        {
            return string.Join("", _capturedByBlack.ToArray());
        }
        public string GetStatusText()
        {
            if (_resignedColor != PieceColor.None)
            {
                PieceColor winner = Opponent(_resignedColor);
                string resigningName = _resignedColor == PieceColor.White ? "White" : "Black";
                string winnerName = winner == PieceColor.White ? "White" : "Black";
                return string.Format("{0} resigns - {1} wins", resigningName, winnerName);
            }
            if (_gameOver)
            {
                if (IsKingInCheck(_sideToMove))
                {
                    PieceColor winner = Opponent(_sideToMove);
                    return string.Format("Checkmate - {0} wins", winner == PieceColor.White ? "White" : "Black");
                }
                return "Draw";
            }
            string side = _sideToMove == PieceColor.White ? "White" : "Black";
            if (IsKingInCheck(_sideToMove)) return side + " to move - in check";
            return side + " to move";
        }
    }
    // -------------------------------------------------------------------
    // SIMPL+ facing wrapper - the only public type in this file. Declared
    // in Chess.usp directly as "Chess game;" (no CREATE OBJECT, no
    // events). Call an action method, then poll Get*() to refresh the UI.
    // -------------------------------------------------------------------
    public class Chess
    {
        private readonly ChessEngine _engine;
        private string _lastRejectReason;
        public Chess()
        {
            _engine = new ChessEngine();
            _lastRejectReason = "";
        }
        /// <summary>Call on a New_Game digital input pulse.</summary>
        public void NewGame()
        {
            _engine.NewGame();
            _lastRejectReason = "";
        }
        /// <summary>
        /// Attempts a move. fromSquare/toSquare are algebraic notation, e.g.
        /// "e2" / "e4". promotionLetter is "Q"/"R"/"B"/"N" (or empty -
        /// defaults to Queen) and is only used when the move is a pawn
        /// promotion. Returns 1 if the move was applied, 0 if rejected -
        /// call GetRejectReason() to find out why when this returns 0.
        /// </summary>
        public ushort MakeMove(SimplSharpString fromSquare, SimplSharpString toSquare, SimplSharpString promotionLetter)
        {
            string from = fromSquare == null ? "" : fromSquare.ToString();
            string to = toSquare == null ? "" : toSquare.ToString();
            string promo = promotionLetter == null ? "" : promotionLetter.ToString();
            char promoChar = promo.Length > 0 ? promo[0] : '\0';
            MoveResult result = _engine.TryMove(from, to, promoChar);
            if (!result.Success)
            {
                switch (result.Code)
                {
                    case MoveResultCode.NotYourTurn: _lastRejectReason = "Not that side's turn"; break;
                    case MoveResultCode.NoPieceOnSquare: _lastRejectReason = "No piece on source square"; break;
                    case MoveResultCode.GameAlreadyOver: _lastRejectReason = "Game is already over"; break;
                    default: _lastRejectReason = "Illegal move"; break;
                }
                return 0;
            }
            _lastRejectReason = "";
            return 1;
        }
        /// <summary>
        /// Has the engine pick and play a move for whichever side is
        /// currently to move (simple material-based heuristic). Returns 1 if
        /// a move was made, 0 if there was no legal move or the game is
        /// already over.
        /// </summary>
        public ushort MakeCpuMove()
        {
            MoveResult result = _engine.MakeCpuMove();
            if (!result.Success)
            {
                switch (result.Code)
                {
                    case MoveResultCode.GameAlreadyOver: _lastRejectReason = "Game is already over"; break;
                    default: _lastRejectReason = "CPU had no legal move"; break;
                }
                return 0;
            }
            _lastRejectReason = "";
            return 1;
        }
        /// <summary>1 = White resigns, 0 = Black resigns.</summary>
        public void Resign(ushort whiteResigns)
        {
            _engine.Resign(whiteResigns == 1 ? PieceColor.White : PieceColor.Black);
        }
        public SimplSharpString GetBoardSquares() { return new SimplSharpString(_engine.GetBoardString()); }
        public SimplSharpString GetLegalDestinationMask(SimplSharpString fromSquare)
        {
            string from = fromSquare == null ? "" : fromSquare.ToString();
            return new SimplSharpString(_engine.GetLegalDestinationMask(from));
        }
        public SimplSharpString GetFEN() { return new SimplSharpString(_engine.GetFEN()); }
        public SimplSharpString GetLastMove() { return new SimplSharpString(_engine.LastMove == null ? "" : _engine.LastMove.ToString()); }
        public SimplSharpString GetStatusText() { return new SimplSharpString(_engine.GetStatusText()); }
        public SimplSharpString GetCapturedByWhite() { return new SimplSharpString(_engine.GetCapturedByWhite()); }
        public SimplSharpString GetCapturedByBlack() { return new SimplSharpString(_engine.GetCapturedByBlack()); }
        public SimplSharpString GetRejectReason() { return new SimplSharpString(_lastRejectReason); }
        public ushort GetWhiteToMove() { return (ushort)(_engine.SideToMove == PieceColor.White ? 1 : 0); }
        public ushort GetWhiteInCheck() { return (ushort)(_engine.IsInCheck(PieceColor.White) ? 1 : 0); }
        public ushort GetBlackInCheck() { return (ushort)(_engine.IsInCheck(PieceColor.Black) ? 1 : 0); }
        public ushort GetCheckmate() { return (ushort)(_engine.LastResultCode == MoveResultCode.OkCheckmate ? 1 : 0); }
        public ushort GetStalemate() { return (ushort)(_engine.LastResultCode == MoveResultCode.OkStalemate ? 1 : 0); }
        public ushort GetDraw()
        {
            bool draw = _engine.LastResultCode == MoveResultCode.OkDrawFiftyMove ||
                        _engine.LastResultCode == MoveResultCode.OkDrawInsufficientMaterial;
            return (ushort)(draw ? 1 : 0);
        }
        public ushort GetGameOver() { return (ushort)(_engine.IsGameOver ? 1 : 0); }
        public ushort GetFullmoveNumber() { return (ushort)_engine.FullmoveNumber; }
    }
}