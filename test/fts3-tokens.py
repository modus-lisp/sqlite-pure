#!/usr/bin/env python3
"""Tokenizer oracle for FTS3/4: random texts run through SQLite's fts3tokenize
virtual table (token bytes, byte offsets, positions), written as s-expressions
for test/fts3-tokens.lisp.     fts3-tokens.py SEED N OUT.sexp"""
import sqlite3, random, sys
seed, n, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
r = random.Random(seed)
pieces = ['hello', 'World', 'ÉCOLE', 'café', 'naïve', 'straße', 'ǅemal', 'Ω', 'σς', 'İstanbul', 'ﬁ', '日本語', '中文',
          'été', '́x', 'áb', 'a_b', 'x-y', "it's", '3.14', '42', '١٢٣', '😀', 'tést', 'ÅNGSTRÖM', 'Ǆ', 'ĳ',
          'running', 'runs', 'happiness', 'relational', 'conditional', 'agreed', 'hopping', 'sky', 'y', 'yyy',
          'generalizations', 'oscillators', 'formality', 'electrical', 'hopeful', 'goodness', 'adjustment',
          'abcdefghijklmnopqrstuvwxyz', 'a1b2c3d4e5f6g7h8i9', 'ABCDEFGHIJKLMNOPQRSTU', 'x$y', 'ÀÉÎÕÜ',
          '\t', '\n', ' ', '  ', ',', '.', ';', '(', ')', '"', "'", '#', '+', '/', ' ', ' ', '　']
stems = ['connect', 'relat', 'generaliz', 'hop', 'run', 'agre', 'formal', 'electric', 'adjust', 'sensit',
         'oscillat', 'happ', 'cry', 'fly', 'probat', 'rate', 'conflat', 'troubl', 'siz', 'fail', 'fil',
         'control', 'roll', 'dress', 'caress', 'pony', 'tie', 'sky', 'feed', 'bleed', 'plaster', 'bor',
         'motor', 'sing', 'crying', 'hope', 'valen', 'hesit', 'digit', 'radic', 'decis', 'depend', 'gyroscop',
         'effect', 'adopt', 'irrit', 'homolog', 'commun', 'activ', 'bowdler', 'defens', 'goodn', 'analog']
suffixes = ['', 's', 'es', 'ed', 'ing', 'ation', 'ational', 'tional', 'ization', 'iveness', 'fulness',
            'ousness', 'aliti', 'iviti', 'biliti', 'ement', 'ment', 'ent', 'ance', 'ence', 'able', 'ible',
            'ize', 'ise', 'ism', 'ist', 'ity', 'ly', 'ness', 'ful', 'al', 'ical', 'icate', 'ative', 'alize',
            'er', 'ers', 'ies', 'ied', 'eed', 'eeds', 'ion', 'ions', 'ou', 'ate', 'iti', 'ous', 'ive', 'y', 'e',
            'll', 'at', 'bl', 'iz', 'sion', 'tion', 'ant', 'ic', 'logi', 'li', 'ously', 'entli', 'eli', 'alli']
words = [s + x for s in stems for x in suffixes] + [s + x + y for s in stems[:12] for x in suffixes[:14] for y in suffixes[:14]]
def text():
    return ''.join(r.choice(pieces) + r.choice([' ', ' ', '', ',', '-']) for _ in range(r.randint(0, 12)))
texts = [text() for _ in range(n)]
texts += [' '.join(words[i:i+50]) for i in range(0, len(words), 50)]
configs = [['simple'], ['porter'], ['unicode61'], ['unicode61', 'remove_diacritics=0'], ['unicode61', 'remove_diacritics=2'],
           ['unicode61', 'tokenchars=-_', 'separators=x'], ['unicode61', 'separators=e\u00e9', 'tokenchars=.\u0301'],
           ['simple', '', '-.x'], ['simple', 'ignored', 'aeiou ']]
def q(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"') + '"'
c = sqlite3.connect(':memory:')
with open(out, 'w', encoding='utf-8') as f:
    f.write('(' + ' '.join(q(t) for t in texts) + ')\n')
    for k, cfg in enumerate(configs):
        c.execute('create virtual table t%d using fts3tokenize(%s)' % (k, ', '.join("'" + a + "'" for a in cfg)))
        cfg = ' '.join('"' + a + '"' for a in cfg)
        out_t = []
        for t in texts:
            rows = c.execute('select hex(token), start, "end", position from t%d where input=?' % k, (t,)).fetchall()
            out_t.append('(' + ' '.join('(%s %d %d %d)' % (q(h), s, e, p) for h, s, e, p in rows) + ')')
        f.write('(%s %s)\n' % (q(cfg), ' '.join(out_t)))
