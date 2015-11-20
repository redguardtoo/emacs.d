import sys
import types

from pydoc import safeimport, resolve, ErrorDuringImport
from pkgutil import iter_modules

from elpy import compat

# Types we want to recurse into (nodes).
CONTAINER_TYPES = (type, types.ModuleType)
# Types of attributes we can get documentation for (leaves).
PYDOC_TYPES = (type,
               types.FunctionType,
               types.BuiltinFunctionType,
               types.BuiltinMethodType,
               types.MethodType,
               types.ModuleType)
if not compat.PYTHON3:  # pragma: nocover
    # Python 2 old style classes
    CONTAINER_TYPES = tuple(list(CONTAINER_TYPES) + [types.ClassType])
    PYDOC_TYPES = tuple(list(PYDOC_TYPES) + [types.ClassType])


def get_pydoc_completions(modulename):
    """Get possible completions for modulename for pydoc.

    Returns a list of possible values to be passed to pydoc.

    """
    modulename = compat.ensure_not_unicode(modulename)
    modulename = modulename.rstrip(".")
    if modulename == "":
        return sorted(get_modules())
    candidates = get_completions(modulename)
    if candidates:
        return sorted(candidates)
    needle = modulename
    if "." in needle:
        modulename, part = needle.rsplit(".", 1)
        candidates = get_completions(modulename)
    else:
        candidates = get_modules()
    return sorted(candidate for candidate in candidates
                  if candidate.startswith(needle))


def get_completions(modulename):
    modules = set("{0}.{1}".format(modulename, module)
                  for module in get_modules(modulename))

    try:
        module, name = resolve(modulename)
    except ImportError:
        return modules
    if isinstance(module, CONTAINER_TYPES):
        modules.update("{0}.{1}".format(modulename, name)
                       for name in dir(module)
                       if not name.startswith("_") and
                       isinstance(getattr(module, name),
                                  PYDOC_TYPES))
    return modules


def get_modules(modulename=None):
    """Return a list of modules and packages under modulename.

    If modulename is not given, return a list of all top level modules
    and packages.

    """
    modulename = compat.ensure_not_unicode(modulename)
    if not modulename:
        try:
            return ([modname for (importer, modname, ispkg)
                     in iter_modules()
                     if not modname.startswith("_")] +
                    list(sys.builtin_module_names))
        except OSError:
            # Bug in Python 2.6, see #275
            return list(sys.builtin_module_names)
    try:
        module = safeimport(modulename)
    except ErrorDuringImport:
        return []
    if module is None:
        return []
    if hasattr(module, "__path__"):
        return [modname for (importer, modname, ispkg)
                in iter_modules(module.__path__)
                if not modname.startswith("_")]
    return []
