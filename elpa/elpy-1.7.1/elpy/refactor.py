"""Refactoring methods for elpy.

This interfaces directly with rope, regardless of the backend used,
because the other backends don't really offer refactoring choices.
Once Jedi is similarly featureful as Rope we can try and offer both.


# Too complex:

- Restructure: Interesting, but too complex, and needs deep Rope
  knowledge to do well.

- ChangeSignature: Slightly less complex interface, but still to
  complex, requiring a large effort for the benefit.


# Too useless:

I could not get these to work in any useful fashion. I might be doing
something wrong.

- ExtractVariable does not replace the code extracted with the
  variable, making it a glorified copy&paste function. Emacs can do
  better than this interface by itself.

- EncapsulateField: Getter/setter methods are outdated, this should be
  using properties.

- IntroduceFactory: Inserts a trivial method to the current class.
  Cute.

- IntroduceParameter: Introduces a parameter correctly, but does not
  replace the old code with the parameter. So it just edits the
  argument list and adds a shiny default.

- LocalToField: Seems to just add "self." in front of all occurrences
  of a variable in the local scope.

- MethodObject: This turns the current method into a callable
  class/object. Not sure what that would be good for.


# Can't even get to work:

- ImportOrganizer expand_star_imports, handle_long_imports,
  relatives_to_absolutes: Seem not to do anything.

- create_move: I was not able to figure out what it would like to see
  as its attrib argument.

"""

from elpy.rpc import Fault

try:
    from rope.base.exceptions import RefactoringError
    from rope.base.project import Project
    from rope.base.libutils import path_to_resource
    from rope.base import change as rope_change
    from rope.base import worder
    from rope.refactor.importutils import ImportOrganizer
    from rope.refactor.topackage import ModuleToPackage
    from rope.refactor.rename import Rename
    from rope.refactor.move import create_move
    from rope.refactor.inline import create_inline
    from rope.refactor.extract import ExtractMethod
    from rope.refactor.usefunction import UseFunction
    ROPE_AVAILABLE = True
except ImportError:
    ROPE_AVAILABLE = False


def options(description, **kwargs):
    """Decorator to set some options on a method."""
    def set_notes(function):
        function.refactor_notes = {'name': function.__name__,
                                   'category': "Miscellaneous",
                                   'description': description,
                                   'doc': getattr(function, '__doc__',
                                                  ''),
                                   'args': []}
        function.refactor_notes.update(kwargs)
        return function
    return set_notes


class Refactor(object):
    """The main refactoring interface.

    Once initialized, the first call should be to get_refactor_options
    to get a list of refactoring options at a given position. The
    returned value will also list any additional options required.

    Once you picked one, you can call get_changes to get the actual
    refactoring changes.

    """
    def __init__(self, project_root, filename):
        self.project_root = project_root
        if ROPE_AVAILABLE:
            self.project = Project(project_root, ropefolder=None)
            self.resource = path_to_resource(self.project, filename)
        else:
            self.project = None
            self.resource = FakeResource(filename)

    def get_refactor_options(self, start, end=None):
        """Return a list of options for refactoring at the given position.

        If `end` is also given, refactoring on a region is assumed.

        Each option is a dictionary of key/value pairs. The value of
        the key 'name' is the one to be used for get_changes.

        The key 'args' contains a list of additional arguments
        required for get_changes.

        """
        result = []
        for symbol in dir(self):
            if not symbol.startswith("refactor_"):
                continue
            method = getattr(self, symbol)
            if not method.refactor_notes.get('available', True):
                continue
            category = method.refactor_notes['category']
            if end is not None and category != 'Region':
                continue
            if end is None and category == 'Region':
                continue
            is_on_symbol = self._is_on_symbol(start)
            if not is_on_symbol and category in ('Symbol', 'Method'):
                continue
            requires_import = method.refactor_notes.get('only_on_imports',
                                                        False)
            if requires_import and not self._is_on_import_statement(start):
                continue
            result.append(method.refactor_notes)
        return result

    def _is_on_import_statement(self, offset):
        "Does this offset point to an import statement?"
        data = self.resource.read()
        bol = data.rfind("\n", 0, offset) + 1
        eol = data.find("\n", 0, bol)
        if eol == -1:
            eol = len(data)
        line = data[bol:eol]
        line = line.strip()
        if line.startswith("import ") or line.startswith("from "):
            return True
        else:
            return False

    def _is_on_symbol(self, offset):
        "Is this offset on a symbol?"
        if not ROPE_AVAILABLE:
            return False
        data = self.resource.read()
        if offset >= len(data):
            return False
        if data[offset] != '_' and not data[offset].isalnum():
            return False
        word = worder.get_name_at(self.resource, offset)
        if word:
            return True
        else:
            return False

    def get_changes(self, name, *args):
        """Return a list of changes for the named refactoring action.

        Changes are dictionaries describing a single action to be
        taken for the refactoring to be successful.

        A change has an action and possibly a type. In the description
        below, the action is before the slash and the type after it.

        change: Change file contents
        - file: The path to the file to change
        - contents: The new contents for the file
        - Diff: A unified diff showing the changes introduced

        create/file: Create a new file
        - file: The file to create

        create/directory: Create a new directory
        - path: The directory to create

        move/file: Rename a file
        - source: The path to the source file
        - destination: The path to the destination file name

        move/directory: Rename a directory
        - source: The path to the source directory
        - destination: The path to the destination directory name

        delete/file: Delete a file
        - file: The file to delete

        delete/directory: Delete a directory
        - path: The directory to delete

        """
        if not name.startswith("refactor_"):
            raise ValueError("Bad refactoring name {0}".format(name))
        method = getattr(self, name)
        if not method.refactor_notes.get('available', True):
            raise RuntimeError("Method not available")
        return method(*args)

    @options("Convert from x import y to import x.y as y", category="Imports",
             args=[("offset", "offset", None)],
             only_on_imports=True,
             available=ROPE_AVAILABLE)
    def refactor_froms_to_imports(self, offset):
        """Converting imports of the form "from ..." to "import ..."."""
        refactor = ImportOrganizer(self.project)
        changes = refactor.froms_to_imports(self.resource, offset)
        return translate_changes(changes)

    @options("Reorganize and clean up", category="Imports",
             available=ROPE_AVAILABLE)
    def refactor_organize_imports(self):
        """Clean up and organize imports."""
        refactor = ImportOrganizer(self.project)
        changes = refactor.organize_imports(self.resource)
        return translate_changes(changes)

    @options("Convert the current module into a package", category="Module",
             available=ROPE_AVAILABLE)
    def refactor_module_to_package(self):
        """Convert the current module into a package."""
        refactor = ModuleToPackage(self.project, self.resource)
        changes = refactor.get_changes()
        return translate_changes(changes)

    @options("Rename symbol at point", category="Symbol",
             args=[("offset", "offset", None),
                   ("new_name", "string", "Rename to: "),
                   ("in_hierarchy", "boolean",
                    "Rename in super-/subclasses as well? "),
                   ("docs", "boolean",
                    "Replace occurences in docs and strings? ")
                   ],
             available=ROPE_AVAILABLE)
    def refactor_rename_at_point(self, offset, new_name, in_hierarchy, docs):
        """Rename the symbol at point."""
        try:
            refactor = Rename(self.project, self.resource, offset)
        except RefactoringError as e:
            raise Fault(str(e), code=400)
        changes = refactor.get_changes(new_name, in_hierarchy=in_hierarchy,
                                       docs=docs)
        return translate_changes(changes)

    @options("Rename current module", category="Module",
             args=[("new_name", "string", "Rename to: ")],
             available=ROPE_AVAILABLE)
    def refactor_rename_current_module(self, new_name):
        """Rename the current module."""
        refactor = Rename(self.project, self.resource, None)
        changes = refactor.get_changes(new_name)
        return translate_changes(changes)

    @options("Move the current module to a different package",
             category="Module",
             args=[("new_name", "directory", "Destination package: ")],
             available=ROPE_AVAILABLE)
    def refactor_move_module(self, new_name):
        """Move the current module."""
        refactor = create_move(self.project, self.resource)
        resource = path_to_resource(self.project, new_name)
        changes = refactor.get_changes(resource)
        return translate_changes(changes)

    @options("Inline function call at point", category="Symbol",
             args=[("offset", "offset", None),
                   ("only_this", "boolean", "Only this occurrence? ")],
             available=ROPE_AVAILABLE)
    def refactor_create_inline(self, offset, only_this):
        """Inline the function call at point."""
        refactor = create_inline(self.project, self.resource, offset)
        if only_this:
            changes = refactor.get_changes(remove=False, only_current=True)
        else:
            changes = refactor.get_changes(remove=True, only_current=False)
        return translate_changes(changes)

    @options("Extract current region as a method", category="Region",
             args=[("start", "start_offset", None),
                   ("end", "end_offset", None),
                   ("name", "string", "Method name: "),
                   ("make_global", "boolean", "Create global method? ")],
             available=ROPE_AVAILABLE)
    def refactor_extract_method(self, start, end, name,
                                make_global):
        """Extract region as a method."""
        refactor = ExtractMethod(self.project, self.resource, start, end)
        changes = refactor.get_changes(name, similar=True, global_=make_global)
        return translate_changes(changes)

    @options("Use the function at point wherever possible", category="Method",
             args=[("offset", "offset", None)],
             available=ROPE_AVAILABLE)
    def refactor_use_function(self, offset):
        """Use the function at point wherever possible."""
        refactor = UseFunction(self.project, self.resource, offset)
        changes = refactor.get_changes()
        return translate_changes(changes)


def translate_changes(initial_change):
    """Translate rope.base.change.Change instances to dictionaries.

    See Refactor.get_changes for an explanation of the resulting
    dictionary.

    """
    agenda = [initial_change]
    result = []
    while agenda:
        change = agenda.pop(0)
        if isinstance(change, rope_change.ChangeSet):
            agenda.extend(change.changes)
        elif isinstance(change, rope_change.ChangeContents):
            result.append({'action': 'change',
                           'file': change.resource.real_path,
                           'contents': change.new_contents,
                           'diff': change.get_description()})
        elif isinstance(change, rope_change.CreateFile):
            result.append({'action': 'create',
                           'type': 'file',
                           'file': change.resource.real_path})
        elif isinstance(change, rope_change.CreateFolder):
            result.append({'action': 'create',
                           'type': 'directory',
                           'path': change.resource.real_path})
        elif isinstance(change, rope_change.MoveResource):
            result.append({'action': 'move',
                           'type': ('directory'
                                    if change.new_resource.is_folder()
                                    else 'file'),
                           'source': change.resource.real_path,
                           'destination': change.new_resource.real_path})
        elif isinstance(change, rope_change.RemoveResource):
            if change.resource.is_folder():
                result.append({'action': 'delete',
                               'type': 'directory',
                               'path': change.resource.real_path})
            else:
                result.append({'action': 'delete',
                               'type': 'file',
                               'file': change.resource.real_path})
    return result


class FakeResource(object):
    """A fake resource in case Rope is absence."""

    def __init__(self, filename):
        self.real_path = filename

    def read(self):
        with open(self.real_path) as f:
            return f.read()
