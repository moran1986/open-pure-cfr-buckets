// Assumes two hole cards.

#include <stdio.h>
#include <stdlib.h>

#include <algorithm>
#include <string>
#include <unordered_set>
#include <vector>
#include <unordered_map>

#include "canonical.h"
#include "cards.h"
#include "constants.h"
#include "hand_tree.h"
#include "io.h"

#include <ctime> // To debug how long shit takes.

using namespace std;

static void GetIBoard(Card *board, unsigned int num_board_cards, Card min_card,
		      unsigned int *i_board) {
  vector<unsigned int> v(num_board_cards);
  for (unsigned int i = 0; i < num_board_cards; ++i) {
    v[i] = board[i] - min_card;
  }
  sort(v.begin(), v.end());
  for (unsigned int i = 0; i < num_board_cards; ++i) {
    i_board[(num_board_cards - 1) - i] = v[i];
  }
}

struct ScoredHandLowerCompare {
  bool operator()(const pair<unsigned int, pair<Card, Card> > &p1,
		  const pair<unsigned int, pair<Card, Card> > &p2) {
    if (p1.first < p2.first) {
      return true;
    } else if (p1.first > p2.first) {
      return false;
    } else {
      if (p1.second.first < p2.second.first) return true;
      else                                   return false;
    }
  }
};
static ScoredHandLowerCompare g_scored_hand_lower_compare;

// Useful for keeping hand lookups in memory. Maps from full hand (in specific, canonical form, to value (float)
typedef unordered_map<unsigned long, float> hand_value_map;
typedef unordered_map<unsigned long, pair<float, long> > hand_average_value_map;
static const int kNumBuckets = 5;

static void ProcessBoardUniform(Card *board, HandTree *hand_tree,
				unsigned int num_board_cards,
				unsigned int num_hole_card_pairs,
				unsigned int num_cards_in_deck,
				Card min_card, Writer *writer) {
  unsigned int i_board[5];
  GetIBoard(board, num_board_cards, min_card, i_board);
  unsigned int i_hole_cards[2];

  // OK here we create a vector for pairs of cards, and a code from hand_tree(??)
  vector< pair<unsigned int, pair<Card, Card> > > hands;
  for (Card hi = min_card + 1; hi <= kMaxCard; ++hi) {
    if (OnBoard(hi, board, num_board_cards)) continue;
    i_hole_cards[0] = hi - min_card;
    for (Card lo = min_card; lo < hi; ++lo) {
      if (OnBoard(lo, board, num_board_cards)) continue;
      i_hole_cards[1] = lo - min_card;
      unsigned int mh_val = hand_tree->Val(i_board, i_hole_cards);
      hands.push_back(make_pair(mh_val, make_pair(hi, lo)));

      // Found valid hand that we need to consider for this board
      // Val == value of the hand. Right?
      OutputTwoCards(hi, lo);
      printf("\thand_tree->Val() = %d\n", mh_val);
    }
  }

  printf("Now sorting hand by g_scored_hand_lower_compare\n");

  sort(hands.begin(), hands.end(), g_scored_hand_lower_compare);

  // Now, we should be able to have all (canonical) hands sorted in order.
  // The rest of the logic is connected to counting winners, losers and ties.

  unsigned int seen[kEndCards];
  for (unsigned int i = min_card; i < (unsigned int)kEndCards; ++i) {
    seen[i] = 0;
  }

  // Not 100% sure how this works, but logic to skip cards in the deck that are canonical?
  unsigned int num_remaining = num_cards_in_deck - num_board_cards - 2;
  unsigned int num_opp_hole_card_pairs =
    num_remaining * (num_remaining - 1) / 2;

  // something about number of cards at each index??
  unsigned short *beats = new unsigned short[num_hole_card_pairs];
  // The number of possible hole card pairs containing a given card
  unsigned int num_buddies = (num_cards_in_deck - num_board_cards) - 1;
  unsigned short i = 0;
  while (i < num_hole_card_pairs) {
    unsigned int mh = hands[i].first;
    unsigned short j = i;
    do {
      Card hi = hands[i].second.first;
      Card lo = hands[i].second.second;
      beats[i] = j - seen[hi] - seen[lo];
      ++i;
    } while (i < num_hole_card_pairs && hands[i].first == mh);

    for (unsigned short k = j; k < i; ++k) {
      Card hi = hands[k].second.first;
      Card lo = hands[k].second.second;
      seen[hi] += 1;
      seen[lo] += 1;
    }

    unsigned short base_lose = num_hole_card_pairs - i;

    printf("Now writing for index i < num_hole_card_pairs %i\n", i);

    for (unsigned short k = j; k < i; ++k) {
      Card hi = hands[k].second.first;
      Card lo = hands[k].second.second;
      // With five-card boards, there should be 46 hole card pairs containing,
      // say, Kc.  52 cards - 5 on board - Kc
      unsigned short lose = base_lose -
	((num_buddies - seen[hi]) + (num_buddies - seen[lo]));
      writer->WriteUnsignedChar(hi);
      writer->WriteUnsignedChar(lo);

      // debug
      OutputTwoCards(hi, lo);

      if (beats[k] > num_opp_hole_card_pairs) {
	fprintf(stderr, "beats out of range?!?  k %i beats %i\n", k,
		beats[k]);
	OutputTwoCards(board);
	printf(" ");
	OutputTwoCards(hi, lo);
	printf("\n");
	exit(-1);
      }
      if (lose > num_opp_hole_card_pairs) {
	fprintf(stderr, "lose out of range: %i?!?  k %i\n", lose, k);
	fprintf(stderr, "base_lose %i nb %i sh %i sl %i\n", base_lose,
		num_buddies, seen[hi], seen[lo]);
	fprintf(stderr, "nhcp %i\n", num_hole_card_pairs);
	exit(-1);
      }
      writer->WriteUnsignedShort(beats[k]);
      writer->WriteUnsignedShort(lose);

      // debug
      printf("\tbeats[k] = %d\tlose = %d\n", beats[k], lose);
    }
  }
  delete [] beats;
}


static void Uniform(Card **canon_boards, unsigned int num_canon_boards) {
  HandTree hand_tree;
  unsigned int max_street = 3;
  unsigned int num_board_cards = 0;
  for (unsigned int s = 1; s <= max_street; ++s) {
    num_board_cards += NumCardsForStreet(s);
  }
  unsigned int num_hole_card_pairs = NumHoleCardPairs(max_street);
  char buf[500];
  unsigned int num_cards_in_deck = NumCardsInDeck();
  Card min_card = MakeCard(2, 0);
  sprintf(buf, "%s/wins_and_losses.holdem.2.0", g_data_root);
  Writer writer(buf);
  unsigned int bd;

  // hack, if we want detailed debug for X number of boards
  bool debug = true;
  unsigned int max_boards = 100;

  for (bd = 0; bd < num_canon_boards && (!debug || bd < max_boards); ++bd) {
    if (bd % 100000 == 0) fprintf(stderr, "Bd %i/%i\n", bd, num_canon_boards);
    // Boards::Board(max_street, bd, board);
    Card *board = canon_boards[bd];

    // debug
    if (debug) OutputFiveCards(board); printf("\tThis is our board! Considering all hands on this board...\n");

    writer.WriteUnsignedInt(bd);
    printf("considering unsigned board %d", bd);
    ProcessBoardUniform(board, &hand_tree, num_board_cards,
			num_hole_card_pairs, num_cards_in_deck, min_card,
			&writer);
  }
}


static Card **GenerateBoards(unsigned int *num_canon_boards) {
  Card **canon_boards = new Card *[2554656];
  unsigned int index = 0;
  unordered_set<unsigned int> seen;
  Card raw_board[5], canon_board[5];
  bool debug = true;
  for (Card flop_hi = kMinCard + 2; flop_hi <= kMaxCard; ++flop_hi) {
    raw_board[0] = flop_hi;
    for (Card flop_mid = kMinCard + 1; flop_mid < flop_hi; ++flop_mid) {
      raw_board[1] = flop_mid;
      for (Card flop_lo = kMinCard; flop_lo < flop_mid; ++flop_lo) {
	raw_board[2] = flop_lo;
	for (Card turn = kMinCard; turn <= kMaxCard; ++turn) {
	  if (OnBoard(turn, raw_board, 3)) continue;
	  raw_board[3] = turn;
	  for (Card river = kMinCard; river <= kMaxCard; ++river) {
	    if (OnBoard(river, raw_board, 4)) continue;
	    raw_board[4] = river;
	    CanonicalizeCards(raw_board, 1, 3, canon_board);
	    unsigned int code = canon_board[0] * 12960000 +
	      canon_board[1] * 216000 + canon_board[2] * 3600 +
	      canon_board[3] * 60 + canon_board[4];
	    if (seen.find(code) == seen.end()) {
	      seen.insert(code);
	      Card *board = new Card[5];
	      for (unsigned int i = 0; i < 5; ++i) {
		board[i] = canon_board[i];
	      }
	      canon_boards[index] = board;
	      ++index;

	      // For debug
	      if (debug && (index % 100000 == 0)) {
		OutputFiveCards(canon_board);
		printf("\tindex %d\tcode %d\n", index, code);
	      }
	    }
	  }
	}
      }
    }
  }
  *num_canon_boards = index;
  fprintf(stderr, "%i canonical boards\n", *num_canon_boards);
  return canon_boards;
}


// Figure out how we can load wins and losses, if already computed on disk!
// A. We need canonical boards in same order.
// B. read output in form
static void ReadWinsLosses(Card **canon_boards, unsigned int num_canon_boards, hand_value_map& hand_map) {
  // Same as generating boards...
  HandTree hand_tree;
  unsigned int max_street = 3;
  unsigned int num_board_cards = 0;
  for (unsigned int s = 1; s <= max_street; ++s) {
    num_board_cards += NumCardsForStreet(s);
  }
  unsigned int num_hole_card_pairs = NumHoleCardPairs(max_street);
  char buf[500];
  //unsigned int num_cards_in_deck = NumCardsInDeck();
  //Card min_card = MakeCard(2, 0);

  //sprintf(buf, "%s/wins_and_losses.holdem.2.0", g_data_root);
  //Writer writer(buf);
  sprintf(buf, "%s/wins_and_losses.holdem.2.0_full", g_data_root);
  Reader reader(buf);

  unsigned int bd;

  // hack, if we want detailed debug for X number of boards
  bool debug = false;
  unsigned int max_boards = 10000000;
  clock_t begin = clock(); // Allow us to measure how long it takes.

  // We want to build a map of <hand_code> to value.
  // See how big and how fast... until we runs out of memory
  int hand_map_max_size = 10000000; // A hack. If we know size, reserve it right away
  //unordered_map <unsigned int, float> hand_map;
  hand_map.reserve(hand_map_max_size); 

  // With what probability, to include each event?
  srand((unsigned int)time(NULL));
  float include_hand_probability = 1.0 * hand_map_max_size / (num_canon_boards * num_hole_card_pairs);
  printf("Looking to sample %d hand results (limited CPU memory). Will include each result with %.3f%% probability", hand_map_max_size, include_hand_probability * 100.0);
  for (bd = 0; bd < num_canon_boards && (!debug || bd < max_boards); ++bd) {
    if (bd % 100000 == 0) {
      clock_t end = clock();
      double elapsed_secs = double(end - begin) / CLOCKS_PER_SEC;
      printf("\nTook %.2f seconds to read %d boards \n", elapsed_secs, bd);
      printf("\n-----------------\nBd %i/%i\n", bd, num_canon_boards);
      debug = true;
    } else {
      debug = false;
    }

    // Boards::Board(max_street, bd, board);
    Card *board = canon_boards[bd];

    // debug
    if (debug) { 
      OutputFiveCards(board); 
      printf("\tThis is our board! Considering all hands on this board...\n");
    }

    // Read board ID. Should match.
    unsigned int bd_read = reader.ReadUnsignedIntOrDie();
    if (debug) printf("Read board id %d\n", bd_read);

    // There should now be 990 hands read? Actually... fewer.
    unsigned int read_hands;
    for (read_hands = 0; read_hands < num_hole_card_pairs; ++read_hands) {
      // Read two cards
      Card hi = reader.ReadUnsignedCharOrDie();
      Card lo = reader.ReadUnsignedCharOrDie();
      //if (debug) OutputTwoCards(hi, lo);
      // read wins and losses
      unsigned short wins = reader.ReadUnsignedShortOrDie();
      unsigned short losses = reader.ReadUnsignedShortOrDie();

      // Also produce hand's allin value... (wins - losses)/990 --> {1.0, -1.0}
      float value = ((wins - losses) / 990.0 + 1.0)/2.0;
      //if (debug) printf("\twins = %d\tlosses = %d\tvalue = %.3f\t[count = %d]\n", wins, losses, value, read_hands);

      // TODO: Put these values in an easy-to-lookup map.
      // But... map from what to what? Ideally, just (hand) -> value.
      // Which means "unordered_map <int, int> m;" if we can encode 7-card hand uniquely in a code.
      unsigned long code_board = board[0] * 12960000 +
	board[1] * 216000 + board[2] * 3600 +
	board[3] * 60 + board[4];
      unsigned long code_board_w_hand = code_board * 3600 + hi * 60 + lo;

      //if (debug) printf("\tcode_board: %d\tcode_board_w_hand: %d\n", code_board, code_board_w_hand);

      // Try a hack. Include hands in the map, with some (small) %.
      // That way, we can consider all flops, but only for some hole cards.
      // Good enough for local testing. Can generate buckets, at least at preflop & flop level.
      float random_float = ((float)rand()/(float)(RAND_MAX)) * 1.0;
      bool included = false;
      if (random_float <= include_hand_probability) {
	// NOTE. Should *never* have a collision. 
	if (hand_map.find(code_board_w_hand) != hand_map.end()) {
	  printf("\nError! Collision on code %lu:\t(", code_board_w_hand);
	  OutputTwoCards(hi, lo); printf(")");
	  OutputFiveCards(board);
	}

	hand_map[code_board_w_hand] = value;
	included = true;
	if (hand_map.size() % 1000000 == 0) {
	  printf("\n--> Map size %lu", hand_map.size());

	  printf("\nValue %.2f. Adding new code %lu:\t(", value, code_board_w_hand);
	  OutputTwoCards(hi, lo); printf(")");
	  OutputFiveCards(board);
	}
      }
    }
  }

  printf("\nloaded %lu items into the hand, value map", hand_map.size());
  printf("\nFinished reading %d boards", bd);
}

// Given map of <code> -> (average, count), return average-value bounds that create approx equal sized num_buckets
// (can assume that all average values [0.0, 1.0]
static void BucketCutoffsFromCounts(hand_average_value_map& hand_averages, const int num_buckets, vector<float>& bucket_cutoffs, 
				    unordered_map< unsigned long, pair<Card, Card> >& preflop_key,
				    unordered_map<unsigned long, unsigned int>& preflop_bucket_assignments) {
  // dump all the counts in a vector, then sort it
  vector< pair<pair<float, long>, unsigned long > > hand_counts;
  long total_hands_count = 0;
  for (hand_average_value_map::iterator hands_iter = hand_averages.begin(); hands_iter != hand_averages.end(); ++hands_iter) {
    hand_counts.push_back(make_pair(hands_iter->second, hands_iter->first));
    total_hands_count += hands_iter->second.second;
  }
  sort(hand_counts.begin(), hand_counts.end()); // can we get away with default sort?

  // Now iterate through the vector, and pump when we hit a bucket break.
  long running_count = 0;
  float breaks[num_buckets+1];

  // To keep overloading... also save buckets. Format: 
  // xxx -- num buckets xxx -- num items (that will be written out)
  char buf[500];
  sprintf(buf, "%s/buckets.holdem.preflop.2.0.9", g_data_root);
  Writer writer(buf);

  // How many buckets, and how many outputs?
  writer.WriteUnsignedInt(num_buckets);
  writer.WriteUnsignedLong(hand_averages.size());

  for(vector< pair<pair<float, long>, unsigned long > >::iterator it = hand_counts.begin(); it != hand_counts.end(); ++it) {
    float val = it->first.first;
    long count = it->first.second;
    unsigned long hand_code = it->second;
    Card hi = preflop_key[hand_code].first;
    Card lo = preflop_key[hand_code].second;
    running_count += count;
    int segment = min((int)((running_count * num_buckets) / total_hands_count + 1), num_buckets);
    OutputTwoCards(hi, lo);
    printf("\t%d/%d - (%.4f, %lu)\n", segment, num_buckets, val, count);
    breaks[segment] = val;
    bucket_cutoffs[segment] = val;

    // For each item, write
    // Cards
    writer.WriteUnsignedChar(hi);
    writer.WriteUnsignedChar(lo);
    // value
    writer.WriteFloat(val);
    // bucket number
    writer.WriteUnsignedInt(segment);

    // And update the value in bucket assignments (useful for next level)
    preflop_bucket_assignments[hand_code] = segment;
  }
  breaks[-1] = 1.0;
  bucket_cutoffs[-1] = 1.0;
  //return breaks;

  
}

// Loop over all possible boards. Do something. 
// We get hand value map. For the lookup, need specific canonical form. Sparse values, so make sure value exists.
static void LoopOverAllBoards(Card **canon_boards, unsigned int num_canon_boards, hand_value_map& hand_map) {
  clock_t begin = clock();

  Card raw_cards[7]; // actual cards
  Card canon_preflop[2], canon_flop[5], canon_cards[7];  // Various canonicals, for all cards, preflop, flop, etc
  // Loop over hole cards

  // General counts. How hany hands do we visit? How many of those found in hand_map array?
  int count = 0;
  int count_misses = 0;
  int count_hits = 0;

  // For preflop bucketing, we also want to collect values for all (canonical) preflop hand
  // A. Set of unique preflop hands seen
  unordered_set<unsigned long> preflop_seen;
  unordered_map< unsigned long, pair<Card, Card> > preflop_key;  
  // B. Average, count for each element [not most efficient, but easy to update, element at a time]
  // Map code --> (average, count) for all observed hands for this canonical preflop hand.
  hand_average_value_map preflop_hand_averages;

  // At the same time, do counts for flop bucketing. 
  // A. All unqiue (preflop + flop) cases observed (in canonical form)
  unordered_set<unsigned long> flop_seen;
  unordered_map< unsigned long, pair<pair<Card, Card>, tuple<Card, Card, Card> > > flop_key;  
  unordered_map< unsigned long, unsigned int> flop_super_bucket; // 
  // B. Running averages for these same codes
  hand_average_value_map flop_hand_averages;

  bool debug = false;
  unsigned int bd;

  // Hack. Set percentage if we want to skip board to go faster
  float include_board_probability = 0.2; // set to 1.0 or high, to use all boards
  for (bd = 0; bd < num_canon_boards; ++bd) {
    if (bd % 100000 == 0) {
      clock_t end = clock();
      double elapsed_secs = double(end - begin) / CLOCKS_PER_SEC;
      printf("\nTook %.2f seconds to read %d boards \n", elapsed_secs, bd);
      printf("\n-----------------\nBd %i/%i\n", bd, num_canon_boards);
      debug = true;
    } else {
      debug = false;
    }

    // hack -- skip 90% of boards -- to speed up flop processing
    if (((float)rand()/(float)(RAND_MAX)) * 1.0 > include_board_probability) {
      continue;
    }

    // Boards::Board(max_street, bd, board);
    Card *board = canon_boards[bd];
    // Unique codes for whole board, just flop, flop & turn
    unsigned long code_board = board[0] * 12960000 +
      board[1] * 216000 + board[2] * 3600 +
      board[3] * 60 + board[4];
    unsigned long code_flop = board[0] * 12960000 +
      board[1] * 216000 + board[2] * 3600;
    unsigned long code_turn = board[0] * 12960000 +
      board[1] * 216000 + board[2] * 3600 +
      board[3] * 60;

    // debug
    if (debug) { 
      OutputFiveCards(board); 
      printf("\tThis is our board! Considering all hands on this board...\n");
    }

    // Now, iterate over all possible hole cards.
    for (Card hi = kMinCard + 1; hi <= kMaxCard; ++hi) {
      if (OnBoard(hi, board, 5)) continue;
      raw_cards[0] = hi;
      for (Card lo = kMinCard; lo < hi; ++lo) {
	if (OnBoard(lo, board, 5)) continue;
	raw_cards[1] = lo;

	// Encode the board, in "raw cards" also. For canonicals.
	raw_cards[2] = board[0];
	raw_cards[3] = board[1];
	raw_cards[4] = board[2];
	raw_cards[5] = board[3];
	raw_cards[6] = board[4];

	// Encode canonical preflops.
	CanonicalizeCards(raw_cards, 0, 0, canon_preflop);
	unsigned long preflop_code = 60 * canon_preflop[0] + canon_preflop[1];
	if (preflop_seen.find(preflop_code) == preflop_seen.end()) {
	  // Only 169 total, so happy to list.
	  printf("\nAdding new preflop hand (%lu):\t", preflop_seen.size()); OutputTwoCards(canon_preflop[0], canon_preflop[1]);
	  preflop_seen.insert(preflop_code);
	  preflop_key[preflop_code] = make_pair(canon_preflop[0], canon_preflop[1]);
	  preflop_hand_averages[preflop_code] = make_pair(0.0, 0);
	}

	// Also, encode canonical flop+pre combination. Why? We want to bucket those also.
	CanonicalizeCards(raw_cards, 0, 1, canon_flop);
	// Assert that flop is is the same as "board"/flop
	if (canon_flop[2] == board[0] && canon_flop[3] == board[1] && canon_flop[4] == board[2]) {
	  // all good
	} else {
	  printf("\nError! Mismatch canonalization on flop. Board: "); OutputFiveCards(board);
	  printf("\t("); OutputTwoCards(hi, lo); printf(")\n");
	  OutputFiveCards(canon_flop);
	}

	unsigned long flop_code = code_flop * 3600 + canon_flop[0] * 60 + canon_flop[1];
	if (flop_seen.find(flop_code) == flop_seen.end()) {
	  // So many outputs... just list 1/10000 [ total]
	  if (flop_seen.size() % 10000 == 0) {
	    printf("\nAdding new canonical flop hand (%lu): (", flop_seen.size()); 
	    OutputTwoCards(canon_flop[0], canon_flop[1]); printf(")");
	    OutputThreeCards(board);
	    printf("\noriginals: "); OutputSevenCards(raw_cards);
	  }
	  flop_seen.insert(flop_code);
	  flop_key[flop_code] = make_pair(make_pair(canon_flop[0], canon_flop[1]), make_tuple(board[0], board[1], board[2]));
	  flop_hand_averages[flop_code] = make_pair(0.0, 0);
	}

      
	// OK, now see if we can evaluate this hand.
	count++;
	
	// A. Canonical for full hand. We don't need it... but creates equivalent lookup. Why not.
	CanonicalizeCards(raw_cards, 0, 3, canon_cards);

	// B. calculate code -- use the raw preflop cards, since we encode 0.0-1.0 value for all preflop combinations
	// TODO: Lookup via canonical representation (equivalent preflop hand)
	unsigned long code_board_w_hand = code_board * 3600 + hi * 60 + lo;
	unsigned long code_board_w_hand_canonical = code_board * 3600 + canon_cards[0] * 60 + canon_cards[1];

	// C. look for value? -- use iter since map already huge... and if we miss, we don't want to add more to it
	hand_value_map::iterator iter = hand_map.find(code_board_w_hand);
	hand_value_map::iterator iter_canonical = hand_map.find(code_board_w_hand_canonical);
	float value = -1.0;
	if (iter != hand_map.end()) {
	  count_hits++;
	  value = iter->second;
	} else if (iter_canonical != hand_map.end()) {
	  count_hits++;
	  value = iter_canonical->second;
	}

	// Did we find something?
	if (value >= 0.0) {
	  // Update value for the correct preflop canonical!
	  int preflop_count = preflop_hand_averages[preflop_code].second + 1;
	  float preflop_average = (preflop_hand_averages[preflop_code].first * preflop_hand_averages[preflop_code].second + value) / preflop_count;
	  preflop_hand_averages[preflop_code] = make_pair(preflop_average, preflop_count);

	  // Similarly, update the flop canonical counts.
	  int flop_count = flop_hand_averages[flop_code].second + 1;
	  float flop_average = (flop_hand_averages[flop_code].first * flop_hand_averages[flop_code].second + value) / flop_count;
	  flop_hand_averages[flop_code] = make_pair(flop_average, flop_count);
	
	  if (count_hits % 50000 == 0) {
	    printf("\ncan:\t(");
	    OutputTwoCards(hi, lo); printf(")"); OutputFiveCards(board);
	    printf(" --> found value %.3f for hand\n", value);
	    OutputTwoCards(canon_preflop[0], canon_preflop[1]);
	    printf("\t updated averge, count to (%.3f, %d)\n(", preflop_hand_averages[preflop_code].first, preflop_hand_averages[preflop_code].second);
	    OutputTwoCards(canon_flop[0], canon_flop[1]); printf(")"); OutputThreeCards(board);
	    printf("\t updated averge, count to (%.3f, %d)\n", flop_hand_averages[flop_code].first, flop_hand_averages[flop_code].second);
	  }
	} else {
	  count_misses++;
	  if (count_misses % 100000000 == 0) {
	    printf("\ncan:\t(");
	    OutputTwoCards(hi, lo); printf(")"); OutputFiveCards(board);
	    printf("\n");
	    printf("--> missing data or error for hand. No value\n");
	  }
	}
      }
    }
  }

  printf("\nFinished. %d cases. Missed %d cases, hit %d cases", count, count_misses, count_hits);

  // Counts for canonical preflop hands 
  printf("\n-------\n");
  printf("\nFound %lu canonical preflop hands. Values for each:\n", preflop_seen.size());
  int count_missing_preflop = 0;
  for (unordered_set<unsigned long>::iterator preflop_iter = preflop_seen.begin(); preflop_iter != preflop_seen.end(); ++preflop_iter) {
    unsigned long preflop_code = *preflop_iter;
    OutputTwoCards(preflop_key[preflop_code].first, preflop_key[preflop_code].second);
    printf("\t%.3f, %d\n", preflop_hand_averages[preflop_code].first, preflop_hand_averages[preflop_code].second);
    if (preflop_hand_averages[preflop_code].second == 0) {
      ++count_missing_preflop;
    }
  }
  printf("\nFound %lu canonical preflop hands. %d missing weights", preflop_seen.size(), count_missing_preflop);
  printf("\n-------\n");

  // Turn map of averages... into cutoffs
  vector<float> bucket_cutoffs(kNumBuckets+1);
  unordered_map<unsigned long, unsigned int> preflop_bucket_assignments; // For next level, we need code -> bucket
  BucketCutoffsFromCounts(preflop_hand_averages, kNumBuckets, bucket_cutoffs, preflop_key, preflop_bucket_assignments);

  // Counts for canonical flop hands
  printf("\n-------\n");
  printf("\nFound %lu canonical flop hands. Values for each:\n", flop_seen.size());
  long count_missing_flops = 0;
  long count_flops = 0;
  for (unordered_set<unsigned long>::iterator flop_iter = flop_seen.begin(); flop_iter != flop_seen.end(); ++flop_iter) {
    unsigned long flop_code = *flop_iter;
    if (count_flops % 10000 == 0) {
      // Compute preflop bucket, via preflop hand.
      // TODO: Should store this in the map, also...
      raw_cards[0] = flop_key[flop_code].first.first;
      raw_cards[1] =  flop_key[flop_code].first.second;
      CanonicalizeCards(raw_cards, 0, 0, canon_preflop);
      unsigned long preflop_code = canon_preflop[0] * 60 + canon_preflop[1];
      unsigned int preflop_bucket = preflop_bucket_assignments[preflop_code];

      // Now print the hand
      OutputTwoCards(flop_key[flop_code].first.first, flop_key[flop_code].first.second); printf("-");
      OutputThreeCards(get<0>(flop_key[flop_code].second), get<1>(flop_key[flop_code].second), get<2>(flop_key[flop_code].second));
      printf("\t%.3f, %d [preflop bucket %d]\n", flop_hand_averages[flop_code].first, flop_hand_averages[flop_code].second, preflop_bucket);
      
    }
    if (flop_hand_averages[flop_code].second == 0) {
      ++count_missing_flops;
    }
    ++count_flops;
  }
  printf("\nFound %lu canonical flop hands. %lu missing weights", flop_seen.size(), count_missing_flops);
  printf("\n-------\n");

  

  clock_t end = clock();
  double elapsed_secs = double(end - begin) / CLOCKS_PER_SEC;
  printf("\nTook %.2f seconds\n", elapsed_secs);
}


static void Usage(const char *prog_name) {
  fprintf(stderr, "USAGE: %s\n", prog_name);
  exit(-1);
}

int main(int argc, char *argv[]) {
  clock_t begin = clock(); // Allow us to measure how long it takes.

  if (argc != 1) Usage(argv[0]);
  Card **canon_boards;
  unsigned int num_canon_boards;
  canon_boards = GenerateBoards(&num_canon_boards);

  clock_t end = clock();
  double elapsed_secs = double(end - begin) / CLOCKS_PER_SEC;
  printf("\nTook %.2f seconds to GenerateBoards \n", elapsed_secs);
  begin = clock();

  // Calculate win/loss values for all hands, on all canonical boards
  // Uniform(canon_boards, num_canon_boards);
  
  // If we already have this data... load it from disk
  hand_value_map hand_map;
  ReadWinsLosses(canon_boards, num_canon_boards, hand_map);

  printf("\n-> loaded %lu items into the hand, value map\n", hand_map.size());

  // TODO: Now call another function, which loops over boards, and looks up existing values,
  // and builds preflop buckets. 
  LoopOverAllBoards(canon_boards, num_canon_boards, hand_map);

  // Next, loop again, and this time build perfect recall flop buckets (bucket on flops... but within preflop buckets)

  end = clock();
  elapsed_secs = double(end - begin) / CLOCKS_PER_SEC;
  printf("\nTook %.2f seconds to ReadWinsLosses \n", elapsed_secs);
}
