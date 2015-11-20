"""Glue for the "importmagic" library.

"""

import os
import sys
import threading


try:
    import importmagic.index
    import importmagic.symbols
    import importmagic.importer
except ImportError:  # pragma: no cover
    importmagic = None


class ImportMagic(object):

    def __init__(self):
        self.is_enabled = bool(importmagic)
        # fail_message is reported to the user when symbol_index
        # is (still) None
        self.fail_message = "symbol index is not yet ready"
        self.project_root = None
        self.symbol_index = None
        self._thread = None

    def _build_symbol_index(self, project_root, custom_path, blacklist_re):
        try:
            index = importmagic.index.SymbolIndex(blacklist_re=blacklist_re)
            if os.environ.get('ELPY_TEST'):
                # test suite support: do not index the whole PYTHONPATH, it
                # takes much too long
                index.build_index([])
            elif custom_path:
                index.build_index(custom_path)
            else:
                index.build_index([project_root] + sys.path)
        except Exception as e:
            self.fail_message = "symbol index failed to build: %s" % e
        else:
            self.symbol_index = index

    def build_index(self, project_root, custom_path=None, blacklist_re=None):
        self.project_root = None
        self._thread = threading.Thread(target=self._build_symbol_index,
                                        args=(project_root, custom_path,
                                              blacklist_re))
        self._thread.setDaemon(True)
        self._thread.start()

    def get_import_symbols(self, symbol):
        scores = self.symbol_index.symbol_scores(symbol)
        return ["from %s import %s" % (mod, var) if var else "import %s" % mod
                for (_, mod, var) in scores]

    def add_import(self, source, statement):
        imports = importmagic.importer.Imports(self.symbol_index, source)
        if statement.startswith('import '):
            imports.add_import(statement[7:])
        else:
            sep = statement.find(' import ')
            if sep > -1:
                imports.add_import_from(statement[5:sep], statement[sep+8:])
        start_line, end_line, import_block = imports.get_update()
        return start_line, end_line, import_block

    def get_unresolved_symbols(self, source):
        scope = importmagic.symbols.Scope.from_source(source)
        unres, unref = scope.find_unresolved_and_unreferenced_symbols()
        return list(unres)

    def remove_unreferenced_imports(self, source):
        scope = importmagic.symbols.Scope.from_source(source)
        unres, unref = scope.find_unresolved_and_unreferenced_symbols()
        # Note: we do not supply "unres" to the call below, since we do
        # not want to add imports without querying the user from which
        # module symbols should be imported.
        start_line, end_line, import_block = importmagic.importer.get_update(
            source, self.symbol_index, set(), unref)
        return start_line, end_line, import_block
