package schema

// Type is an interface that all types in the schema implement.
// Currently, these are ObjectType and EnumType.
type Type interface {
	// TypeName returns the type's name.
	TypeName() string

	// Validate validates the type.
	Validate(TypeSet) error

	// isType is a private method that ensures that only types in this package can be marked as types.
	isType()
}

// TypeSet represents something that has types and allows them to be looked up by name.
// Currently, the only implementation is ModuleSchema.
type TypeSet interface {
	// LookupType looks up a type by name.
	LookupType(name string) (t Type, found bool)

	// LookupEnumType is a convenience method that looks up an EnumType by name.
	LookupEnumType(name string) (t EnumType, found bool)

	// LookupObjectType is a convenience method that looks up an ObjectType by name.
	LookupObjectType(name string) (t ObjectType, found bool)

	// AllTypes calls the given function for each type in the type set.
	// This function is compatible with go 1.23 iterators and can be used like this:
	// for t := range types.AllTypes {
	//     // do something with t
	// }
	AllTypes(f func(Type) bool)

	// EnumTypes calls the given function for each EnumType in the type set.
	// This function is compatible with go 1.23 iterators.
	EnumTypes(f func(EnumType) bool)

	// ObjectTypes calls the given function for each ObjectType in the type set.
	// This function is compatible with go 1.23 iterators.
	ObjectTypes(f func(ObjectType) bool)

	// isTypeSet is a private method that ensures that only types in this package can be marked as type sets.
	isTypeSet()
}

// EmptyTypeSet is a schema that contains no types.
// It can be used in Validate methods when there is no schema needed or available.
func EmptyTypeSet() TypeSet {
	return emptyTypeSetInst
}

var emptyTypeSetInst = emptyTypeSet{}

type emptyTypeSet struct{}

func (emptyTypeSet) LookupType(string) (Type, bool) {
	return nil, false
}

func (s emptyTypeSet) LookupEnumType(string) (t EnumType, found bool) {
	return EnumType{}, false
}

func (s emptyTypeSet) LookupObjectType(string) (t ObjectType, found bool) {
	return ObjectType{}, false
}

func (emptyTypeSet) AllTypes(func(Type) bool) {}

func (s emptyTypeSet) EnumTypes(func(EnumType) bool) {}

func (s emptyTypeSet) ObjectTypes(func(ObjectType) bool) {}

func (emptyTypeSet) isTypeSet() {}