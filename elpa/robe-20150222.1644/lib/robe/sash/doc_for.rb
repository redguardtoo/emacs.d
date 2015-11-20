require 'pry'
begin
  require 'pry-doc' if RUBY_ENGINE == "ruby"
rescue LoadError
  # Whatever, it's optional.
end

module Robe
  class Sash
    class DocFor
      def initialize(method)
        @method = method
      end

      def format
        info = self.class.method_struct(@method)
        {docstring: info.docstring,
         source: info.source,
         aliases: info.aliases,
         visibility: visibility}
      end

      def visibility
        owner, name = @method.owner, @method.name
        if owner.public_instance_methods(false).include?(name)
          :public
        elsif owner.protected_instance_methods(false).include?(name)
          :protected
        elsif owner.private_instance_methods(false).include?(name)
          :private
        end
      end

      def self.method_struct(method)
        begin
          info = Pry::Method.new(method)

          if info.dynamically_defined?
            doc = ""
            source = "# This method was defined outside of a source file."
          else
            doc = info.doc
            source = (info.source? ? info.source : "# Not available.")
          end

          OpenStruct.new(docstring: doc, source: source,
                         aliases: info.aliases.map(&:to_sym))
        rescue Pry::CommandError
          message = $!.message =~ /pry-doc/ ? $!.message : ""
          return OpenStruct.new(docstring: message)
        end
      end
    end
  end
end
