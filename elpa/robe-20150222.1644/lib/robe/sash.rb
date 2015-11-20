require 'robe/sash/doc_for'
require 'robe/type_space'
require 'robe/scanners'
require 'robe/visor'
require 'robe/jvisor'

module Robe
  class Sash
    attr_accessor :visor

    def initialize(visor = pick_visor)
      @visor = visor
    end

    def class_locations(name, mod)
      locations = {}
      if (obj = visor.resolve_context(name, mod)) and obj.is_a? Module
        methods = obj.methods(false).map { |m| obj.method(m) } +
                  obj.instance_methods(false).map { |m| obj.instance_method(m) }
        methods.each do |m|
          if loc = m.source_location
            path = loc[0]
            locations[path] ||= 0
            locations[path] += 1
          end
        end
      end
      if defined? Class.class_attribute and Class != obj
        locations.delete Class.method(:class_attribute).source_location[0]
      end
      locations.keys.sort { |k1, k2| -(locations[k1] <=> locations[k2]) }
    end

    def modules
      visor.each_object(Module).map(&:__name__).compact
    end

    def targets(obj)
      obj = visor.resolve_const(obj)
      if obj.is_a? Module
        module_methods = obj.methods.map { |m| method_spec(obj.method(m)) }
        instance_methods = (obj.instance_methods +
                            obj.private_instance_methods(false))
          .map { |m| method_spec(obj.instance_method(m)) }
        [obj.__name__] + module_methods + instance_methods
      else
        self.targets(obj.class.to_s)
      end
    end

    def find_method(mod, inst, sym)
      mod.__send__(inst ? :instance_method : :method, sym)
    end

    def find_method_owner(mod, inst, sym)
      begin
        find_method(mod, inst, sym).owner
      rescue NameError
      end
    end

    def method_spec(method)
      owner, inst = method.owner, nil
      if !owner.__singleton_class__?
        name, inst = method_owner_and_inst(owner)
      else
        name = owner.to_s[/Class:([A-Z][^\(>]*)/, 1] # defined in an eigenclass
      end
      [name, inst, method.name, method.parameters] + method.source_location.to_a
    end

    def method_owner_and_inst(owner)
      if owner.__name__
        [owner.__name__, true]
      else
        unless owner.is_a?(Class)
          mod, inst = nil, true
          ObjectSpace.each_object(Module) do |m|
            if m.__include__?(owner) && m.__name__
              mod = m
            elsif m.__singleton_class__.__include__?(owner)
              mod = m
              inst = nil
            end && break
          end
          [mod && mod.__name__, inst]
        end
      end
    end

    def doc_for(mod, type, sym)
      mod = visor.resolve_const(mod)
      DocFor.new(find_method(mod, type, sym.to_sym)).format
    end

    def method_targets(name, target, mod, instance, superc, conservative)
      sym = name.to_sym
      space = TypeSpace.new(visor, target, mod, instance, superc)
      special_method = sym == :initialize || superc
      scanner = ModuleScanner.new(sym, special_method || !target)

      space.scan_with(scanner)

      if (targets = scanner.candidates).any?
        owner = find_method_owner(space.target_type, instance, sym)
        if owner
          targets.reject! do |method|
            !(method.owner <= owner) &&
              targets.find { |other| other.owner < method.owner }
          end
        end
      elsif (target || !conservative) && !special_method
        unless target
          scanner.scan_methods(Kernel, :private_instance_methods)
        end
        scanner.check_private = false
        scanner.scan(visor.each_object(Module), true, true)
      end

      scanner.candidates.map { |method| method_spec(method) }
        .sort_by { |(mname)| mname ? mname.scan(/::/).length : 99 }
    end

    def complete_method(prefix, target, mod, instance)
      space = TypeSpace.new(visor, target, mod, instance, nil)
      scanner = MethodScanner.new(prefix, !target)

      space.scan_with(scanner)

      if scanner.candidates.empty?
        scanner.check_private = false
        scanner.scan(visor.each_object(Module), true, true)
      end

      scanner.candidates.map { |m| method_spec(m) }
    end

    def complete_const(prefix, mod)
      colons = prefix.rindex("::")
      tail = colons ? prefix[colons + 2..-1] : prefix
      if !colons
        path = [Object]
        path += visor.resolve_path(mod) if mod
        path.flat_map do |m|
          complete_const_in_module(tail, m)
        end
      else
        base_name = prefix[0..colons + 1]
        base = unless colons == 0
                 if mod
                   visor.resolve_context(base_name[0..-3], mod)
                 else
                   visor.resolve_const(base_name)
                 end
               end
        complete_const_in_module(tail, base || Object)
      end.map { |c| "#{base_name}#{c}" }
    end

    def complete_const_in_module(tail, base)
      base.constants.grep(/^#{Regexp.escape(tail)}/)
    end

    def rails_refresh
      ActionDispatch::Reloader.cleanup!
      ActionDispatch::Reloader.prepare!
      Rails.application.eager_load!
    end

    def ping
      "pong"
    end

    def call(path, body)
      _, endpoint, *args = path.split("/").map { |s| s == "-" ? nil : s }
      value = public_send(endpoint.to_sym, *args)
      value.to_json
    end

    private

    def pick_visor
      if RUBY_ENGINE == "jruby"
        JVisor.new
      else
        Visor.new
      end
    end
  end
end

class Module
  unless method_defined?(:__name__)
    alias_method :__name__, :name
  end

  if method_defined?(:singleton_class?)
    alias_method :__singleton_class__?, :singleton_class?
  else
    def __singleton_class__?
      self != Class && ancestors.first != self
    end
  end

  unless method_defined?(:__singleton_class__)
    alias_method :__singleton_class__, :singleton_class
  end

  unless method_defined?(:__include__?)
    alias_method :__include__?, :include?
  end
end
