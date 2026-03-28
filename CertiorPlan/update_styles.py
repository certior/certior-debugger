import sys

file_path = "/home/pbour/certior-mvp/app/frontend/src/pages/releases.tsx"

with open(file_path, "r") as f:
    content = f.read()

# Fix layout/header container
content = content.replace(
    '<div className="max-w-5xl mx-auto space-y-6">',
    '<div className="p-6 lg:p-8 max-w-6xl mx-auto space-y-8">'
)

content = content.replace(
    '''<header>
          <h1 className="text-3xl font-bold tracking-tight text-white mb-2">Release Trust Pipeline</h1>
          <p className="text-gray-400">Evaluate release readiness, review component provenance, and compare with stable baselines.</p>
        </header>''',
    '''<div className="hero-band rounded-[30px] border border-base-700/60 px-6 py-6 shadow-sm">
          <div className="flex flex-col gap-3 lg:flex-row lg:items-end lg:justify-between">
            <div>
              <p className="label mb-2">Release Pipeline</p>
              <h1 className="text-3xl font-semibold font-display text-slate-900 mb-2">Release Trust</h1>
              <p className="max-w-2xl text-sm leading-6 text-slate-600">Evaluate release readiness, review component provenance, and compare with stable baselines.</p>
            </div>
          </div>
        </div>'''
)

# Fix form styling
content = content.replace(
    'className="flex flex-col sm:flex-row gap-4 p-4 bg-[#111] rounded-lg border border-gray-800"',
    'className="flex flex-col sm:flex-row gap-4 p-4 panel-warm rounded-[24px] border border-base-700/60 shadow-sm"'
)

content = content.replace(
    'className="flex-1 bg-black border border-gray-700 text-white rounded px-4 py-2 focus:border-blue-500 focus:outline-none"',
    'className="flex-1 bg-white border border-base-700/50 text-slate-900 rounded-xl px-4 py-2 focus:ring-2 focus:ring-accent-500 focus:outline-none text-sm placeholder:text-slate-400"'
)

content = content.replace(
    'className="w-full sm:w-48 bg-black border border-gray-700 text-white rounded px-4 py-2 focus:border-blue-500 focus:outline-none"',
    'className="w-full sm:w-48 bg-white border border-base-700/50 text-slate-900 rounded-xl px-4 py-2 focus:ring-2 focus:ring-accent-500 focus:outline-none text-sm placeholder:text-slate-400"'
)

content = content.replace(
    'className="bg-blue-600 hover:bg-blue-700 text-white font-medium px-6 py-2 rounded focus:outline-none focus:ring-2 focus:ring-blue-500 disabled:opacity-50"',
    'className="btn-primary px-6 rounded-xl text-sm font-medium items-center justify-center flex"'
)

# Dark theme text swaps
content = content.replace('bg-green-900/20 border-green-500/40', 'bg-emerald-50 border-emerald-200/60 text-emerald-800')
content = content.replace('bg-red-900/20 border-red-500/40', 'bg-rose-50 border-rose-200/60 text-rose-800')
content = content.replace('text-green-400', 'text-emerald-700')
content = content.replace('text-red-400', 'text-rose-700')
content = content.replace('bg-red-500/30 border border-red-500/50 text-red-100', 'bg-rose-100 border border-rose-200 text-rose-800')

content = content.replace('text-gray-300', 'text-slate-700')
content = content.replace('text-gray-400', 'text-slate-500')
content = content.replace('text-gray-200', 'text-slate-700')
content = content.replace('text-white', 'text-slate-900')

content = content.replace('bg-[#111]', 'panel-warm')
content = content.replace('bg-[#1a1a1a]', 'panel-warm')
content = content.replace('bg-[#222]', 'panel-base')
content = content.replace('bg-black', 'bg-white')
content = content.replace('bg-gray-800', 'bg-base-700/50')
content = content.replace('bg-gray-900', 'panel-warm')

content = content.replace('border-gray-800', 'border-base-700/50')
content = content.replace('border-gray-700', 'border-base-700/50')
content = content.replace('border-gray-600', 'border-base-700/80')
content = content.replace('border-blue-500', 'border-accent-500')
content = content.replace('text-blue-400', 'text-accent-700')
content = content.replace('text-blue-500', 'text-accent-700')
content = content.replace('text-gray-500', 'text-slate-500')

content = content.replace('className="p-4 bg-red-900/40 border border-red-500/50 rounded-md text-red-200"', 'className="p-4 bg-rose-50 border border-rose-200 rounded-md text-rose-800 text-sm"')


with open(file_path, "w") as f:
    f.write(content)
