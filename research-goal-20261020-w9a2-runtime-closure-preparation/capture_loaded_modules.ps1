param([Parameter(Mandatory=$true)][int]$ObservedProcessId)
$ErrorActionPreference = 'Stop'
$observedProcess = Get-Process -Id $ObservedProcessId -ErrorAction Stop
[pscustomobject]@{
  Scope = 'Read-only existing-process PE module path snapshot; no process mutation'
  CapturedAtUTC = [DateTime]::UtcNow.ToString('o')
  Id = $observedProcess.Id
  ProcessName = $observedProcess.ProcessName
  StartTimeUTC = $observedProcess.StartTime.ToUniversalTime().ToString('o')
  CPU = $observedProcess.CPU
  Executable = $observedProcess.Path
  Modules = @($observedProcess.Modules | ForEach-Object {
    [pscustomobject]@{Name=$_.ModuleName; Path=$_.FileName; Bytes=$_.ModuleMemorySize;
                     BaseAddress=$_.BaseAddress.ToInt64()}
  })
} | ConvertTo-Json -Depth 6
