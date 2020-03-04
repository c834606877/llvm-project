//===-- ClangExternalASTSourceCallbacks.h -----------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef liblldb_ClangExternalASTSourceCallbacks_h_
#define liblldb_ClangExternalASTSourceCallbacks_h_

#include "Plugins/TypeSystem/Clang/TypeSystemClang.h"
#include "clang/Basic/Module.h"

namespace lldb_private {

class ClangExternalASTSourceCallbacks : public clang::ExternalASTSource {
  /// LLVM RTTI support.
  static char ID;

public:
  /// LLVM RTTI support.
  bool isA(const void *ClassID) const override { return ClassID == &ID; }
  static bool classof(const clang::ExternalASTSource *s) { return s->isA(&ID); }

  ClangExternalASTSourceCallbacks(TypeSystemClang &ast) : m_ast(ast) {}

  void FindExternalLexicalDecls(
      const clang::DeclContext *DC,
      llvm::function_ref<bool(clang::Decl::Kind)> IsKindWeWant,
      llvm::SmallVectorImpl<clang::Decl *> &Result) override;

  void CompleteType(clang::TagDecl *tag_decl) override;

  void CompleteType(clang::ObjCInterfaceDecl *objc_decl) override;

  bool layoutRecordType(
      const clang::RecordDecl *Record, uint64_t &Size, uint64_t &Alignment,
      llvm::DenseMap<const clang::FieldDecl *, uint64_t> &FieldOffsets,
      llvm::DenseMap<const clang::CXXRecordDecl *, clang::CharUnits>
          &BaseOffsets,
      llvm::DenseMap<const clang::CXXRecordDecl *, clang::CharUnits>
          &VirtualBaseOffsets) override;

  TypeSystemClang &GetTypeSystem() const { return m_ast; }

  /// Module-related methods.
  /// \{
  llvm::Optional<clang::ExternalASTSource::ASTSourceDescriptor>
  getSourceDescriptor(unsigned ID) override;
  clang::Module *getModule(unsigned ID) override;
  OptionalClangModuleID RegisterModule(clang::Module *module);
  OptionalClangModuleID GetIDForModule(clang::Module *module);
  /// \}
private:
  TypeSystemClang &m_ast;
  std::vector<clang::Module *> m_modules;
  llvm::DenseMap<clang::Module *, unsigned> m_ids;
};

} // namespace lldb_private

#endif // liblldb_ClangExternalASTSourceCallbacks_h_
