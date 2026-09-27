#!/usr/bin/env python3
"""Tokenizer oracle: random texts tokenized by SQLite's FTS5 tokenizers
(via fts5vocab 'instance'), written as s-expressions for
test/fts5-tokens.lisp.     fts5-tokens.py SEED N OUT.sexp"""
import sqlite3, random, sys, os
seed, n, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
r = random.Random(seed)
pieces = ['hello', 'World', 'ÉCOLE', 'café', 'naïve', 'straße', 'ǅemal', 'Ω', 'σς', 'İstanbul', 'ﬁ', '日本語', '中文',
          'été', '́x', 'a_b', 'x-y', "it's", '3.14', '42', '١٢٣', '😀', 'tést', 'ÅNGSTRÖM',
          'running', 'runs', 'happiness', 'relational', 'conditional', 'agreed', 'hopping', 'sky', 'y', 'yyy',
          'generalizations', 'oscillators', 'formality', 'electrical', 'hopeful', 'goodness', 'adjustment',
          '\t', '\n', ' ', '  ', ',', '.', ';', '(', ')', '"', "'", '#', '+', '/', ' ', ' ', '　']
words = []
if os.path.exists('/usr/share/dict/words'):
    words = [w.strip() for w in open('/usr/share/dict/words', encoding='utf-8', errors='ignore')]
else:
    # a synthetic English-ish vocabulary for the stemmer
    stems = ['connect', 'relat', 'generaliz', 'hop', 'run', 'agre', 'formal', 'electric', 'adjust', 'sensit',
             'oscillat', 'happ', 'cry', 'fly', 'probat', 'rate', 'conflat', 'troubl', 'siz', 'fail', 'fil',
             'control', 'roll', 'dress', 'caress', 'pony', 'tie', 'sky', 'feed', 'bleed', 'plaster', 'bor',
             'motor', 'sing', 'crying', 'hope', 'valen', 'hesit', 'digit', 'radic', 'decis', 'depend', 'gyroscop']
    suffixes = ['', 's', 'es', 'ed', 'ing', 'ation', 'ational', 'tional', 'ization', 'iveness', 'fulness',
                'ousness', 'aliti', 'iviti', 'biliti', 'ement', 'ment', 'ent', 'ance', 'ence', 'able', 'ible',
                'ize', 'ise', 'ism', 'ist', 'ity', 'ly', 'ness', 'ful', 'al', 'ical', 'icate', 'ative', 'alize',
                'er', 'ers', 'ies', 'ied', 'eed', 'eeds', 'ion', 'ions', 'ou', 'ate', 'iti', 'ous', 'ive', 'y', 'e', 'll']
    words = [s + x for s in stems for x in suffixes] + [s + x + y for s in stems[:10] for x in suffixes[:12] for y in suffixes[:12]]
def text():
    return ''.join(r.choice(pieces) + r.choice([' ', ' ', '', ',', '-']) for _ in range(r.randint(0, 12)))
texts = [text() for _ in range(n)]
texts += [' '.join(words[i:i+50]) for i in range(0, len(words), 50)]
configs = ['unicode61', 'unicode61 remove_diacritics 0', 'unicode61 remove_diacritics 2',
           "unicode61 tokenchars '-_' separators 'x'", 'ascii', "ascii tokenchars '_.'",
           'porter', 'porter unicode61 remove_diacritics 0', 'trigram', 'trigram case_sensitive 1']
def q(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"') + '"'
c = sqlite3.connect(':memory:')
with open(out, 'w', encoding='utf-8') as f:
    f.write('(' + ' '.join(q(t) for t in texts) + ')\n')
    for k, cfg in enumerate(configs):
        c.execute('create virtual table t%d using fts5(x, tokenize="%s")' % (k, cfg))
        c.execute("create virtual table v%d using fts5vocab(t%d, 'instance')" % (k, k))
        c.executemany('insert into t%d(rowid, x) values(?, ?)' % k, ((i + 1, t) for i, t in enumerate(texts)))
        toks = [[] for _ in texts]
        for doc, term in c.execute('select doc, term from v%d order by doc, offset' % k):
            toks[doc - 1].append(term)
        f.write('(%s %s)\n' % (q(cfg), ' '.join('(' + ' '.join(q(x) for x in t) + ')' for t in toks)))
