"""Method implementations for the Elpy JSON-RPC server.

This file implements the methods exported by the JSON-RPC server. It
handles backend selection and passes methods on to the selected
backend.

"""
import io
import os
import pydoc

from elpy.pydocutils import get_pydoc_completions
from elpy.rpc import JSONRPCServer, Fault
from elpy.impmagic import ImportMagic


try:
    from elpy import jedibackend
except ImportError:  # pragma: no cover
    jedibackend = None

try:
    from elpy import ropebackend
except ImportError:  # pragma: no cover
    ropebackend = None


class ElpyRPCServer(JSONRPCServer):
    """The RPC server for elpy.

    See the rpc_* methods for exported method documentation.

    """
    def __init__(self):
        super(ElpyRPCServer, self).__init__()
        self.backend = None
        self.import_magic = ImportMagic()
        self.project_root = None

    def _call_backend(self, method, default, *args, **kwargs):
        """Call the backend method with args.

        If there is currently no backend, return default."""
        meth = getattr(self.backend, method, None)
        if meth is None:
            return default
        else:
            return meth(*args, **kwargs)

    def rpc_echo(self, *args):
        """Return the arguments.

        This is a simple test method to see if the protocol is
        working.

        """
        return args

    def rpc_init(self, options):
        self.project_root = options["project_root"]

        if self.import_magic.is_enabled:
            self.import_magic.build_index(self.project_root)

        if ropebackend and options["backend"] == "rope":
            self.backend = ropebackend.RopeBackend(self.project_root)
        elif jedibackend and options["backend"] == "jedi":
            self.backend = jedibackend.JediBackend(self.project_root)
        elif ropebackend:
            self.backend = ropebackend.RopeBackend(self.project_root)
        elif jedibackend:
            self.backend = jedibackend.JediBackend(self.project_root)
        else:
            self.backend = None

        return {
            'backend': (self.backend.name if self.backend is not None
                        else None)
        }

    def rpc_get_calltip(self, filename, source, offset):
        """Get the calltip for the function at the offset.

        """
        return self._call_backend("rpc_get_calltip", None, filename,
                                  get_source(source), offset)

    def rpc_get_completions(self, filename, source, offset):
        """Get a list of completion candidates for the symbol at offset.

        """
        results = self._call_backend("rpc_get_completions", [], filename,
                                     get_source(source), offset)
        # Uniquify by name
        results = list(dict((res['name'], res) for res in results)
                       .values())
        results.sort(key=lambda cand: _pysymbol_key(cand["name"]))
        return results

    def rpc_get_completion_docstring(self, completion):
        """Return documentation for a previously returned completion.

        """
        return self._call_backend("rpc_get_completion_docstring",
                                  None, completion)

    def rpc_get_completion_location(self, completion):
        """Return the location for a previously returned completion.

        This returns a list of [file name, line number].

        """
        return self._call_backend("rpc_get_completion_location", None,
                                  completion)

    def rpc_get_definition(self, filename, source, offset):
        """Get the location of the definition for the symbol at the offset.

        """
        return self._call_backend("rpc_get_definition", None, filename,
                                  get_source(source), offset)

    def rpc_get_docstring(self, filename, source, offset):
        """Get the docstring for the symbol at the offset.

        """
        return self._call_backend("rpc_get_docstring", None, filename,
                                  get_source(source), offset)

    def rpc_get_pydoc_completions(self, name=None):
        """Return a list of possible strings to pass to pydoc.

        If name is given, the strings are under name. If not, top
        level modules are returned.

        """
        return get_pydoc_completions(name)

    def rpc_get_pydoc_documentation(self, symbol):
        """Get the Pydoc documentation for the given symbol.

        Uses pydoc and can return a string with backspace characters
        for bold highlighting.

        """
        try:
            docstring = pydoc.render_doc(str(symbol),
                                         "Elpy Pydoc Documentation for %s",
                                         False)
        except (ImportError, pydoc.ErrorDuringImport):
            return None
        else:
            if isinstance(docstring, bytes):
                docstring = docstring.decode("utf-8", "replace")
            return docstring

    def rpc_get_refactor_options(self, filename, start, end=None):
        """Return a list of possible refactoring options.

        This list will be filtered depending on whether it's
        applicable at the point START and possibly the region between
        START and END.

        """
        try:
            from elpy import refactor
        except:
            raise ImportError("Rope not installed, refactorings unavailable")
        ref = refactor.Refactor(self.project_root, filename)
        return ref.get_refactor_options(start, end)

    def rpc_refactor(self, filename, method, args):
        """Return a list of changes from the refactoring action.

        A change is a dictionary describing the change. See
        elpy.refactor.translate_changes for a description.

        """
        try:
            from elpy import refactor
        except:
            raise ImportError("Rope not installed, refactorings unavailable")
        if args is None:
            args = ()
        ref = refactor.Refactor(self.project_root, filename)
        return ref.get_changes(method, *args)

    def rpc_get_usages(self, filename, source, offset):
        """Get usages for the symbol at point.

        """
        source = get_source(source)
        if hasattr(self.backend, "rpc_get_usages"):
            return self.backend.rpc_get_usages(filename, source, offset)
        else:
            raise Fault("get_usages not implemented by current backend",
                        code=400)

    def _ensure_import_magic(self):  # pragma: no cover
        if not self.import_magic.is_enabled:
            raise Fault("fixup_imports not enabled; install importmagic module",
                        code=400)
        if not self.import_magic.symbol_index:
            raise Fault(self.import_magic.fail_message, code=200)  # XXX code?

    def rpc_get_import_symbols(self, filename, source, symbol):
        """Return a list of modules from which the given symbol can be imported.

        """
        self._ensure_import_magic()
        return self.import_magic.get_import_symbols(symbol)

    def rpc_add_import(self, filename, source, statement):
        """Add an import statement to the module.

        """
        self._ensure_import_magic()
        source = get_source(source)
        return self.import_magic.add_import(source, statement)

    def rpc_get_unresolved_symbols(self, filename, source):
        """Return a list of unreferenced symbols in the module.

        """
        self._ensure_import_magic()
        source = get_source(source)
        return self.import_magic.get_unresolved_symbols(source)

    def rpc_remove_unreferenced_imports(self, filename, source):
        """Remove unused import statements.

        """
        self._ensure_import_magic()
        source = get_source(source)
        return self.import_magic.remove_unreferenced_imports(source)


def get_source(fileobj):
    """Translate fileobj into file contents.

    fileobj is either a string or a dict. If it's a string, that's the
    file contents. If it's a string, then the filename key contains
    the name of the file whose contents we are to use.

    If the dict contains a true value for the key delete_after_use,
    the file should be deleted once read.

    """
    if not isinstance(fileobj, dict):
        return fileobj
    else:
        try:
            with io.open(fileobj["filename"], encoding="utf-8") as f:
                return f.read()
        finally:
            if fileobj.get('delete_after_use'):
                try:
                    os.remove(fileobj["filename"])
                except:  # pragma: no cover
                    pass


def _pysymbol_key(name):
    """Return a sortable key index for name.

    Sorting is case-insensitive, with the first underscore counting as
    worse than any character, but subsequent underscores do not. This
    means that dunder symbols (like __init__) are sorted after symbols
    that start with an alphabetic character, but before those that
    start with only a single underscore.

    """
    if name.startswith("_"):
        name = "~" + name[1:]
    return name.lower()
